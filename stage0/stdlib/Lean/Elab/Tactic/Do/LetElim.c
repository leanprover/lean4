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
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_KVMap_setNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_mergeBy(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setValue(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "uses"};
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(183, 67, 224, 192, 49, 118, 23, 147)}};
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "BVar index out of bounds: "};
static const lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUses___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUses___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " >= "};
static const lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUses___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUses___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUses___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__5;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object*, lean_object*, lean_object*);
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
uint8_t v_x_21__boxed_69_; uint8_t v_y_22__boxed_70_; uint8_t v_res_71_; lean_object* v_r_72_; 
v_x_21__boxed_69_ = lean_unbox(v_x_67_);
v_y_22__boxed_70_ = lean_unbox(v_y_68_);
v_res_71_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_x_21__boxed_69_, v_y_22__boxed_70_);
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
uint8_t v_x_18__boxed_99_; uint8_t v_x_19__boxed_100_; uint8_t v_res_101_; lean_object* v_r_102_; 
v_x_18__boxed_99_ = lean_unbox(v_x_97_);
v_x_19__boxed_100_ = lean_unbox(v_x_98_);
v_res_101_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x_18__boxed_99_, v_x_19__boxed_100_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
if (lean_obj_tag(v_x_124_) == 0)
{
return v_x_123_;
}
else
{
lean_object* v_key_125_; lean_object* v_value_126_; lean_object* v_tail_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_150_; 
v_key_125_ = lean_ctor_get(v_x_124_, 0);
v_value_126_ = lean_ctor_get(v_x_124_, 1);
v_tail_127_ = lean_ctor_get(v_x_124_, 2);
v_isSharedCheck_150_ = !lean_is_exclusive(v_x_124_);
if (v_isSharedCheck_150_ == 0)
{
v___x_129_ = v_x_124_;
v_isShared_130_ = v_isSharedCheck_150_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_tail_127_);
lean_inc(v_value_126_);
lean_inc(v_key_125_);
lean_dec(v_x_124_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_150_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; uint64_t v___x_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v_fold_135_; uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v___x_138_; size_t v___x_139_; size_t v___x_140_; size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_131_ = lean_array_get_size(v_x_123_);
v___x_132_ = l_Lean_instHashableFVarId_hash(v_key_125_);
v___x_133_ = 32ULL;
v___x_134_ = lean_uint64_shift_right(v___x_132_, v___x_133_);
v_fold_135_ = lean_uint64_xor(v___x_132_, v___x_134_);
v___x_136_ = 16ULL;
v___x_137_ = lean_uint64_shift_right(v_fold_135_, v___x_136_);
v___x_138_ = lean_uint64_xor(v_fold_135_, v___x_137_);
v___x_139_ = lean_uint64_to_usize(v___x_138_);
v___x_140_ = lean_usize_of_nat(v___x_131_);
v___x_141_ = ((size_t)1ULL);
v___x_142_ = lean_usize_sub(v___x_140_, v___x_141_);
v___x_143_ = lean_usize_land(v___x_139_, v___x_142_);
v___x_144_ = lean_array_uget_borrowed(v_x_123_, v___x_143_);
lean_inc(v___x_144_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 2, v___x_144_);
v___x_146_ = v___x_129_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_key_125_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_value_126_);
lean_ctor_set(v_reuseFailAlloc_149_, 2, v___x_144_);
v___x_146_ = v_reuseFailAlloc_149_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; 
v___x_147_ = lean_array_uset(v_x_123_, v___x_143_, v___x_146_);
v_x_123_ = v___x_147_;
v_x_124_ = v_tail_127_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(lean_object* v_i_151_, lean_object* v_source_152_, lean_object* v_target_153_){
_start:
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = lean_array_get_size(v_source_152_);
v___x_155_ = lean_nat_dec_lt(v_i_151_, v___x_154_);
if (v___x_155_ == 0)
{
lean_dec_ref(v_source_152_);
lean_dec(v_i_151_);
return v_target_153_;
}
else
{
lean_object* v_es_156_; lean_object* v___x_157_; lean_object* v_source_158_; lean_object* v_target_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v_es_156_ = lean_array_fget(v_source_152_, v_i_151_);
v___x_157_ = lean_box(0);
v_source_158_ = lean_array_fset(v_source_152_, v_i_151_, v___x_157_);
v_target_159_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_target_153_, v_es_156_);
v___x_160_ = lean_unsigned_to_nat(1u);
v___x_161_ = lean_nat_add(v_i_151_, v___x_160_);
lean_dec(v_i_151_);
v_i_151_ = v___x_161_;
v_source_152_ = v_source_158_;
v_target_153_ = v_target_159_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(lean_object* v_data_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_nbuckets_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_164_ = lean_array_get_size(v_data_163_);
v___x_165_ = lean_unsigned_to_nat(2u);
v_nbuckets_166_ = lean_nat_mul(v___x_164_, v___x_165_);
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = lean_box(0);
v___x_169_ = lean_mk_array(v_nbuckets_166_, v___x_168_);
v___x_170_ = lean_array_propagate_mark(v_data_163_, v___x_169_);
v___x_171_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v___x_167_, v_data_163_, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(lean_object* v_a_172_, lean_object* v_x_173_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
uint8_t v___x_174_; 
v___x_174_ = 0;
return v___x_174_;
}
else
{
lean_object* v_key_175_; lean_object* v_tail_176_; uint8_t v___x_177_; 
v_key_175_ = lean_ctor_get(v_x_173_, 0);
v_tail_176_ = lean_ctor_get(v_x_173_, 2);
v___x_177_ = l_Lean_instBEqFVarId_beq(v_key_175_, v_a_172_);
if (v___x_177_ == 0)
{
v_x_173_ = v_tail_176_;
goto _start;
}
else
{
return v___x_177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg___boxed(lean_object* v_a_179_, lean_object* v_x_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_179_, v_x_180_);
lean_dec(v_x_180_);
lean_dec(v_a_179_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(uint8_t v_x3_183_, lean_object* v_x_184_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_box(v_x3_183_);
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
else
{
lean_object* v_val_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_197_; 
v_val_187_ = lean_ctor_get(v_x_184_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_197_ == 0)
{
v___x_189_ = v_x_184_;
v_isShared_190_ = v_isSharedCheck_197_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_val_187_);
lean_dec(v_x_184_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_197_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
uint8_t v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_191_ = lean_unbox(v_val_187_);
lean_dec(v_val_187_);
v___x_192_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x3_183_, v___x_191_);
v___x_193_ = lean_box(v___x_192_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_193_);
v___x_195_ = v___x_189_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0___boxed(lean_object* v_x3_198_, lean_object* v_x_199_){
_start:
{
uint8_t v_x3_855__boxed_200_; lean_object* v_res_201_; 
v_x3_855__boxed_200_ = lean_unbox(v_x3_198_);
v_res_201_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_855__boxed_200_, v_x_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(uint8_t v_x3_202_, lean_object* v_a_203_, lean_object* v_x_204_){
_start:
{
if (lean_obj_tag(v_x_204_) == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v_val_207_; lean_object* v___x_208_; 
v___x_205_ = lean_box(0);
v___x_206_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_202_, v___x_205_);
v_val_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_val_207_);
lean_dec(v___x_206_);
v___x_208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_208_, 0, v_a_203_);
lean_ctor_set(v___x_208_, 1, v_val_207_);
lean_ctor_set(v___x_208_, 2, v_x_204_);
return v___x_208_;
}
else
{
lean_object* v_key_209_; lean_object* v_value_210_; lean_object* v_tail_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_226_; 
v_key_209_ = lean_ctor_get(v_x_204_, 0);
v_value_210_ = lean_ctor_get(v_x_204_, 1);
v_tail_211_ = lean_ctor_get(v_x_204_, 2);
v_isSharedCheck_226_ = !lean_is_exclusive(v_x_204_);
if (v_isSharedCheck_226_ == 0)
{
v___x_213_ = v_x_204_;
v_isShared_214_ = v_isSharedCheck_226_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_tail_211_);
lean_inc(v_value_210_);
lean_inc(v_key_209_);
lean_dec(v_x_204_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_226_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
uint8_t v___x_215_; 
v___x_215_ = l_Lean_instBEqFVarId_beq(v_key_209_, v_a_203_);
if (v___x_215_ == 0)
{
lean_object* v_tail_216_; lean_object* v___x_218_; 
v_tail_216_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_202_, v_a_203_, v_tail_211_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 2, v_tail_216_);
v___x_218_ = v___x_213_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_key_209_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_value_210_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_tail_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v_val_222_; lean_object* v___x_224_; 
lean_dec(v_key_209_);
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v_value_210_);
v___x_221_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_202_, v___x_220_);
v_val_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_222_);
lean_dec(v___x_221_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 1, v_val_222_);
lean_ctor_set(v___x_213_, 0, v_a_203_);
v___x_224_ = v___x_213_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_203_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_val_222_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v_tail_211_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___boxed(lean_object* v_x3_227_, lean_object* v_a_228_, lean_object* v_x_229_){
_start:
{
uint8_t v_x3_887__boxed_230_; lean_object* v_res_231_; 
v_x3_887__boxed_230_ = lean_unbox(v_x3_227_);
v_res_231_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_887__boxed_230_, v_a_228_, v_x_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(uint8_t v_x3_232_, lean_object* v_m_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_size_235_; lean_object* v_buckets_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_285_; 
v_size_235_ = lean_ctor_get(v_m_233_, 0);
v_buckets_236_ = lean_ctor_get(v_m_233_, 1);
v_isSharedCheck_285_ = !lean_is_exclusive(v_m_233_);
if (v_isSharedCheck_285_ == 0)
{
v___x_238_ = v_m_233_;
v_isShared_239_ = v_isSharedCheck_285_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_buckets_236_);
lean_inc(v_size_235_);
lean_dec(v_m_233_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_285_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v___x_243_; uint64_t v_fold_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v___x_247_; size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; size_t v___x_251_; size_t v___x_252_; lean_object* v_bkt_253_; uint8_t v___x_254_; 
v___x_240_ = lean_array_get_size(v_buckets_236_);
v___x_241_ = l_Lean_instHashableFVarId_hash(v_a_234_);
v___x_242_ = 32ULL;
v___x_243_ = lean_uint64_shift_right(v___x_241_, v___x_242_);
v_fold_244_ = lean_uint64_xor(v___x_241_, v___x_243_);
v___x_245_ = 16ULL;
v___x_246_ = lean_uint64_shift_right(v_fold_244_, v___x_245_);
v___x_247_ = lean_uint64_xor(v_fold_244_, v___x_246_);
v___x_248_ = lean_uint64_to_usize(v___x_247_);
v___x_249_ = lean_usize_of_nat(v___x_240_);
v___x_250_ = ((size_t)1ULL);
v___x_251_ = lean_usize_sub(v___x_249_, v___x_250_);
v___x_252_ = lean_usize_land(v___x_248_, v___x_251_);
v_bkt_253_ = lean_array_uget_borrowed(v_buckets_236_, v___x_252_);
v___x_254_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_234_, v_bkt_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v_size_x27_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v_buckets_x27_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_255_ = lean_unsigned_to_nat(1u);
v_size_x27_256_ = lean_nat_add(v_size_235_, v___x_255_);
lean_dec(v_size_235_);
v___x_257_ = lean_box(v_x3_232_);
lean_inc(v_bkt_253_);
v___x_258_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_258_, 0, v_a_234_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
lean_ctor_set(v___x_258_, 2, v_bkt_253_);
v_buckets_x27_259_ = lean_array_uset(v_buckets_236_, v___x_252_, v___x_258_);
v___x_260_ = lean_unsigned_to_nat(4u);
v___x_261_ = lean_nat_mul(v_size_x27_256_, v___x_260_);
v___x_262_ = lean_unsigned_to_nat(3u);
v___x_263_ = lean_nat_div(v___x_261_, v___x_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_array_get_size(v_buckets_x27_259_);
v___x_265_ = lean_nat_dec_le(v___x_263_, v___x_264_);
lean_dec(v___x_263_);
if (v___x_265_ == 0)
{
lean_object* v_val_266_; lean_object* v___x_268_; 
v_val_266_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_259_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v_val_266_);
lean_ctor_set(v___x_238_, 0, v_size_x27_256_);
v___x_268_ = v___x_238_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_size_x27_256_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_val_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
else
{
lean_object* v___x_271_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v_buckets_x27_259_);
lean_ctor_set(v___x_238_, 0, v_size_x27_256_);
v___x_271_ = v___x_238_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_size_x27_256_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_buckets_x27_259_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
else
{
lean_object* v___x_273_; lean_object* v_buckets_x27_274_; lean_object* v_bkt_x27_275_; lean_object* v___y_277_; uint8_t v___x_282_; 
lean_inc(v_bkt_253_);
v___x_273_ = lean_box(0);
v_buckets_x27_274_ = lean_array_uset(v_buckets_236_, v___x_252_, v___x_273_);
lean_inc(v_a_234_);
v_bkt_x27_275_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_232_, v_a_234_, v_bkt_253_);
v___x_282_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_234_, v_bkt_x27_275_);
lean_dec(v_a_234_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_unsigned_to_nat(1u);
v___x_284_ = lean_nat_sub(v_size_235_, v___x_283_);
lean_dec(v_size_235_);
v___y_277_ = v___x_284_;
goto v___jp_276_;
}
else
{
v___y_277_ = v_size_235_;
goto v___jp_276_;
}
v___jp_276_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = lean_array_uset(v_buckets_x27_274_, v___x_252_, v_bkt_x27_275_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___x_278_);
lean_ctor_set(v___x_238_, 0, v___y_277_);
v___x_280_ = v___x_238_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___y_277_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___boxed(lean_object* v_x3_286_, lean_object* v_m_287_, lean_object* v_a_288_){
_start:
{
uint8_t v_x3_935__boxed_289_; lean_object* v_res_290_; 
v_x3_935__boxed_289_ = lean_unbox(v_x3_286_);
v_res_290_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v_x3_935__boxed_289_, v_m_287_, v_a_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(lean_object* v_x_291_, lean_object* v_x_292_){
_start:
{
if (lean_obj_tag(v_x_292_) == 0)
{
return v_x_291_;
}
else
{
lean_object* v_key_293_; lean_object* v_value_294_; lean_object* v_tail_295_; uint8_t v___x_296_; lean_object* v___x_297_; 
v_key_293_ = lean_ctor_get(v_x_292_, 0);
lean_inc(v_key_293_);
v_value_294_ = lean_ctor_get(v_x_292_, 1);
lean_inc(v_value_294_);
v_tail_295_ = lean_ctor_get(v_x_292_, 2);
lean_inc(v_tail_295_);
lean_dec_ref_known(v_x_292_, 3);
v___x_296_ = lean_unbox(v_value_294_);
lean_dec(v_value_294_);
v___x_297_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v___x_296_, v_x_291_, v_key_293_);
v_x_291_ = v___x_297_;
v_x_292_ = v_tail_295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(lean_object* v_as_299_, size_t v_i_300_, size_t v_stop_301_, lean_object* v_b_302_){
_start:
{
uint8_t v___x_303_; 
v___x_303_ = lean_usize_dec_eq(v_i_300_, v_stop_301_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; size_t v___x_306_; size_t v___x_307_; 
v___x_304_ = lean_array_uget_borrowed(v_as_299_, v_i_300_);
lean_inc(v___x_304_);
v___x_305_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(v_b_302_, v___x_304_);
v___x_306_ = ((size_t)1ULL);
v___x_307_ = lean_usize_add(v_i_300_, v___x_306_);
v_i_300_ = v___x_307_;
v_b_302_ = v___x_305_;
goto _start;
}
else
{
return v_b_302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2___boxed(lean_object* v_as_309_, lean_object* v_i_310_, lean_object* v_stop_311_, lean_object* v_b_312_){
_start:
{
size_t v_i_boxed_313_; size_t v_stop_boxed_314_; lean_object* v_res_315_; 
v_i_boxed_313_ = lean_unbox_usize(v_i_310_);
lean_dec(v_i_310_);
v_stop_boxed_314_ = lean_unbox_usize(v_stop_311_);
lean_dec(v_stop_311_);
v_res_315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_as_309_, v_i_boxed_313_, v_stop_boxed_314_, v_b_312_);
lean_dec_ref(v_as_309_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add(lean_object* v_a_316_, lean_object* v_b_317_){
_start:
{
lean_object* v_buckets_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v_buckets_318_ = lean_ctor_get(v_a_316_, 1);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_array_get_size(v_buckets_318_);
v___x_321_ = lean_nat_dec_lt(v___x_319_, v___x_320_);
if (v___x_321_ == 0)
{
return v_b_317_;
}
else
{
size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; 
v___x_322_ = ((size_t)0ULL);
v___x_323_ = lean_usize_of_nat(v___x_320_);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_buckets_318_, v___x_322_, v___x_323_, v_b_317_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add___boxed(lean_object* v_a_325_, lean_object* v_b_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_a_325_, v_b_326_);
lean_dec_ref(v_a_325_);
return v_res_327_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(lean_object* v_00_u03b2_328_, lean_object* v_a_329_, lean_object* v_x_330_){
_start:
{
uint8_t v___x_331_; 
v___x_331_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_329_, v_x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___boxed(lean_object* v_00_u03b2_332_, lean_object* v_a_333_, lean_object* v_x_334_){
_start:
{
uint8_t v_res_335_; lean_object* v_r_336_; 
v_res_335_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(v_00_u03b2_332_, v_a_333_, v_x_334_);
lean_dec(v_x_334_);
lean_dec(v_a_333_);
v_r_336_ = lean_box(v_res_335_);
return v_r_336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1(lean_object* v_00_u03b2_337_, lean_object* v_data_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_data_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_340_, lean_object* v_i_341_, lean_object* v_source_342_, lean_object* v_target_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v_i_341_, v_source_342_, v_target_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_x_346_, v_x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(lean_object* v_x_351_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
lean_object* v___x_352_; 
v___x_352_ = lean_unsigned_to_nat(0u);
return v___x_352_;
}
else
{
lean_object* v___x_353_; 
v___x_353_ = lean_unsigned_to_nat(1u);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg___boxed(lean_object* v_x_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(v_x_354_);
lean_dec(v_x_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(lean_object* v_n_356_, lean_object* v_x_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(v_x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___boxed(lean_object* v_n_359_, lean_object* v_x_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(v_n_359_, v_x_360_);
lean_dec(v_x_360_);
lean_dec(v_n_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(lean_object* v_t_362_, lean_object* v_k_363_){
_start:
{
if (lean_obj_tag(v_t_362_) == 0)
{
return v_k_363_;
}
else
{
lean_object* v_uses_364_; lean_object* v___x_365_; 
v_uses_364_ = lean_ctor_get(v_t_362_, 0);
lean_inc_ref(v_uses_364_);
lean_dec_ref_known(v_t_362_, 1);
v___x_365_ = lean_apply_1(v_k_363_, v_uses_364_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(lean_object* v_n_366_, lean_object* v_motive_367_, lean_object* v_ctorIdx_368_, lean_object* v_t_369_, lean_object* v_h_370_, lean_object* v_k_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_369_, v_k_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___boxed(lean_object* v_n_373_, lean_object* v_motive_374_, lean_object* v_ctorIdx_375_, lean_object* v_t_376_, lean_object* v_h_377_, lean_object* v_k_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(v_n_373_, v_motive_374_, v_ctorIdx_375_, v_t_376_, v_h_377_, v_k_378_);
lean_dec(v_ctorIdx_375_);
lean_dec(v_n_373_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___redArg(lean_object* v_t_380_, lean_object* v_none_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_380_, v_none_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim(lean_object* v_n_383_, lean_object* v_motive_384_, lean_object* v_t_385_, lean_object* v_h_386_, lean_object* v_none_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_385_, v_none_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___boxed(lean_object* v_n_389_, lean_object* v_motive_390_, lean_object* v_t_391_, lean_object* v_h_392_, lean_object* v_none_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Elab_Tactic_Do_BVarUses_none_elim(v_n_389_, v_motive_390_, v_t_391_, v_h_392_, v_none_393_);
lean_dec(v_n_389_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___redArg(lean_object* v_t_395_, lean_object* v_some_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_395_, v_some_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim(lean_object* v_n_398_, lean_object* v_motive_399_, lean_object* v_t_400_, lean_object* v_h_401_, lean_object* v_some_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_400_, v_some_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___boxed(lean_object* v_n_404_, lean_object* v_motive_405_, lean_object* v_t_406_, lean_object* v_h_407_, lean_object* v_some_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Elab_Tactic_Do_BVarUses_some_elim(v_n_404_, v_motive_405_, v_t_406_, v_h_407_, v_some_408_);
lean_dec(v_n_404_);
return v_res_409_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12));
v___x_435_ = l_Lean_mkAtom(v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13);
v___x_437_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_438_ = lean_array_push(v___x_437_, v___x_436_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_439_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14);
v___x_440_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11));
v___x_441_ = lean_box(2);
v___x_442_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_440_);
lean_ctor_set(v___x_442_, 2, v___x_439_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15);
v___x_444_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_445_ = lean_array_push(v___x_444_, v___x_443_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_446_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16);
v___x_447_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9));
v___x_448_ = lean_box(2);
v___x_449_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___x_447_);
lean_ctor_set(v___x_449_, 2, v___x_446_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17);
v___x_451_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_452_ = lean_array_push(v___x_451_, v___x_450_);
return v___x_452_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_453_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18);
v___x_454_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7));
v___x_455_ = lean_box(2);
v___x_456_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___x_454_);
lean_ctor_set(v___x_456_, 2, v___x_453_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19);
v___x_458_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_459_ = lean_array_push(v___x_458_, v___x_457_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_460_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20);
v___x_461_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4));
v___x_462_ = lean_box(2);
v___x_463_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___x_461_);
lean_ctor_set(v___x_463_, 2, v___x_460_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1(void){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21);
return v___x_464_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(lean_object* v_numBVars_465_, lean_object* v_n_466_, lean_object* v_i_467_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = lean_nat_sub(v_numBVars_465_, v___x_468_);
v___x_470_ = lean_nat_sub(v___x_469_, v_n_466_);
lean_dec(v___x_469_);
v___x_471_ = lean_nat_dec_eq(v_i_467_, v___x_470_);
lean_dec(v___x_470_);
if (v___x_471_ == 0)
{
uint8_t v___x_472_; 
v___x_472_ = 0;
return v___x_472_;
}
else
{
uint8_t v___x_473_; 
v___x_473_ = 1;
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed(lean_object* v_numBVars_474_, lean_object* v_n_475_, lean_object* v_i_476_){
_start:
{
uint8_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(v_numBVars_474_, v_n_475_, v_i_476_);
lean_dec(v_i_476_);
lean_dec(v_n_475_);
lean_dec(v_numBVars_474_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(lean_object* v_numBVars_479_, lean_object* v_n_480_){
_start:
{
lean_object* v___f_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
lean_inc(v_numBVars_479_);
v___f_481_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_481_, 0, v_numBVars_479_);
lean_closure_set(v___f_481_, 1, v_n_480_);
v___x_482_ = l_Array_ofFn___redArg(v_numBVars_479_, v___f_481_);
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single(lean_object* v_numBVars_484_, lean_object* v_n_485_, lean_object* v_x_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(v_numBVars_484_, v_n_485_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop(lean_object* v_numBVars_492_, lean_object* v_x_493_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v___x_494_; 
v___x_494_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0));
return v___x_494_;
}
else
{
lean_object* v_uses_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_508_; 
v_uses_495_ = lean_ctor_get(v_x_493_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v_x_493_);
if (v_isSharedCheck_508_ == 0)
{
v___x_497_ = v_x_493_;
v_isShared_498_ = v_isSharedCheck_508_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_uses_495_);
lean_dec(v_x_493_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_508_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_nat_add(v_numBVars_492_, v___x_499_);
v___x_501_ = lean_nat_sub(v___x_500_, v___x_499_);
lean_dec(v___x_500_);
v___x_502_ = lean_array_fget(v_uses_495_, v___x_501_);
lean_dec(v___x_501_);
v___x_503_ = lean_array_pop(v_uses_495_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_503_);
v___x_505_ = v___x_497_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_507_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; 
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_502_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
return v___x_506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop___boxed(lean_object* v_numBVars_509_, lean_object* v_x_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_Elab_Tactic_Do_BVarUses_pop(v_numBVars_509_, v_x_510_);
lean_dec(v_numBVars_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(lean_object* v_as_512_, lean_object* v_bs_513_, lean_object* v_i_514_, lean_object* v_cs_515_){
_start:
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = lean_array_get_size(v_as_512_);
v___x_517_ = lean_nat_dec_lt(v_i_514_, v___x_516_);
if (v___x_517_ == 0)
{
lean_dec(v_i_514_);
return v_cs_515_;
}
else
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_array_get_size(v_bs_513_);
v___x_519_ = lean_nat_dec_lt(v_i_514_, v___x_518_);
if (v___x_519_ == 0)
{
lean_dec(v_i_514_);
return v_cs_515_;
}
else
{
lean_object* v_a_520_; lean_object* v_b_521_; uint8_t v___x_522_; uint8_t v___x_523_; uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v_a_520_ = lean_array_fget_borrowed(v_as_512_, v_i_514_);
v_b_521_ = lean_array_fget_borrowed(v_bs_513_, v_i_514_);
v___x_522_ = lean_unbox(v_a_520_);
v___x_523_ = lean_unbox(v_b_521_);
v___x_524_ = l_Lean_Elab_Tactic_Do_Uses_add(v___x_522_, v___x_523_);
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_add(v_i_514_, v___x_525_);
lean_dec(v_i_514_);
v___x_527_ = lean_box(v___x_524_);
v___x_528_ = lean_array_push(v_cs_515_, v___x_527_);
v_i_514_ = v___x_526_;
v_cs_515_ = v___x_528_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0___boxed(lean_object* v_as_530_, lean_object* v_bs_531_, lean_object* v_i_532_, lean_object* v_cs_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(v_as_530_, v_bs_531_, v_i_532_, v_cs_533_);
lean_dec_ref(v_bs_531_);
lean_dec_ref(v_as_530_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(lean_object* v_a_537_, lean_object* v_b_538_){
_start:
{
if (lean_obj_tag(v_a_537_) == 0)
{
return v_b_538_;
}
else
{
if (lean_obj_tag(v_b_538_) == 0)
{
lean_object* v_uses_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
v_uses_539_ = lean_ctor_get(v_a_537_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v_a_537_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v_a_537_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_uses_539_);
lean_dec(v_a_537_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_uses_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
else
{
lean_object* v_uses_547_; lean_object* v_uses_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_558_; 
v_uses_547_ = lean_ctor_get(v_a_537_, 0);
lean_inc_ref(v_uses_547_);
lean_dec_ref_known(v_a_537_, 1);
v_uses_548_ = lean_ctor_get(v_b_538_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v_b_538_);
if (v_isSharedCheck_558_ == 0)
{
v___x_550_ = v_b_538_;
v_isShared_551_ = v_isSharedCheck_558_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_uses_548_);
lean_dec(v_b_538_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_558_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0));
v___x_554_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(v_uses_547_, v_uses_548_, v___x_552_, v___x_553_);
lean_dec_ref(v_uses_548_);
lean_dec_ref(v_uses_547_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_554_);
v___x_556_ = v___x_550_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add(lean_object* v_numBVars_559_, lean_object* v_a_560_, lean_object* v_b_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(v_a_560_, v_b_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___boxed(lean_object* v_numBVars_563_, lean_object* v_a_564_, lean_object* v_b_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Elab_Tactic_Do_BVarUses_add(v_numBVars_563_, v_a_564_, v_b_565_);
lean_dec(v_numBVars_563_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instAddBVarUses(lean_object* v_numBVars_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_BVarUses_add___boxed), 3, 1);
lean_closure_set(v___x_568_, 0, v_numBVars_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2___redArg(lean_object* v_f_569_, lean_object* v_x_570_){
_start:
{
lean_object* v_fst_571_; lean_object* v_snd_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_580_; 
v_fst_571_ = lean_ctor_get(v_x_570_, 0);
v_snd_572_ = lean_ctor_get(v_x_570_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_x_570_);
if (v_isSharedCheck_580_ == 0)
{
v___x_574_ = v_x_570_;
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_snd_572_);
lean_inc(v_fst_571_);
lean_dec(v_x_570_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_576_ = lean_apply_1(v_f_569_, v_fst_571_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_576_);
v___x_578_ = v___x_574_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_snd_572_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2(lean_object* v_00_u03b1_u2081_581_, lean_object* v_00_u03b1_u2082_582_, lean_object* v_00_u03b2_583_, lean_object* v_f_584_, lean_object* v_x_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v_f_584_, v_x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0(lean_object* v_x_587_, lean_object* v_new_588_, lean_object* v_x_589_){
_start:
{
lean_inc_ref(v_new_588_);
return v_new_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed(lean_object* v_x_590_, lean_object* v_new_591_, lean_object* v_x_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Elab_Tactic_Do_addMData___lam__0(v_x_590_, v_new_591_, v_x_592_);
lean_dec_ref(v_x_592_);
lean_dec_ref(v_new_591_);
lean_dec(v_x_590_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData(lean_object* v_d_595_, lean_object* v_e_596_){
_start:
{
if (lean_obj_tag(v_e_596_) == 10)
{
lean_object* v_data_597_; lean_object* v_expr_598_; lean_object* v___f_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_data_597_ = lean_ctor_get(v_e_596_, 0);
lean_inc(v_data_597_);
v_expr_598_ = lean_ctor_get(v_e_596_, 1);
lean_inc_ref(v_expr_598_);
lean_dec_ref_known(v_e_596_, 2);
v___f_599_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_addMData___closed__0));
v___x_600_ = l_Lean_KVMap_mergeBy(v___f_599_, v_d_595_, v_data_597_);
lean_dec(v_data_597_);
v___x_601_ = l_Lean_Expr_mdata___override(v___x_600_, v_expr_598_);
return v___x_601_;
}
else
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Expr_mdata___override(v_d_595_, v_e_596_);
return v___x_602_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(lean_object* v_e_603_){
_start:
{
uint8_t v___y_605_; 
switch(lean_obj_tag(v_e_603_))
{
case 1:
{
uint8_t v___x_607_; 
v___x_607_ = 0;
return v___x_607_;
}
case 5:
{
uint8_t v___x_608_; 
v___x_608_ = l_Lean_Meta_Simp_isOfNatNatLit(v_e_603_);
if (v___x_608_ == 0)
{
uint8_t v___x_609_; 
v___x_609_ = l_Lean_Meta_Simp_isOfScientificLit(v_e_603_);
v___y_605_ = v___x_609_;
goto v___jp_604_;
}
else
{
v___y_605_ = v___x_608_;
goto v___jp_604_;
}
}
case 6:
{
uint8_t v___x_610_; 
v___x_610_ = 0;
return v___x_610_;
}
case 7:
{
uint8_t v___x_611_; 
v___x_611_ = 0;
return v___x_611_;
}
case 8:
{
uint8_t v___x_612_; 
v___x_612_ = 0;
return v___x_612_;
}
case 10:
{
lean_object* v_expr_613_; 
v_expr_613_ = lean_ctor_get(v_e_603_, 1);
v_e_603_ = v_expr_613_;
goto _start;
}
case 11:
{
lean_object* v_struct_615_; 
v_struct_615_ = lean_ctor_get(v_e_603_, 2);
v_e_603_ = v_struct_615_;
goto _start;
}
default: 
{
uint8_t v___x_617_; 
v___x_617_ = 1;
return v___x_617_;
}
}
v___jp_604_:
{
if (v___y_605_ == 0)
{
uint8_t v___x_606_; 
v___x_606_ = l_Lean_Meta_Simp_isCharLit(v_e_603_);
return v___x_606_;
}
else
{
return v___y_605_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup___boxed(lean_object* v_e_618_){
_start:
{
uint8_t v_res_619_; lean_object* v_r_620_; 
v_res_619_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_e_618_);
lean_dec_ref(v_e_618_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0(lean_object* v_val_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v_val_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(lean_object* v_msgData_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v___x_629_; lean_object* v_env_630_; lean_object* v___x_631_; lean_object* v_toCold_632_; lean_object* v_mctx_633_; lean_object* v_lctx_634_; lean_object* v_options_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_629_ = lean_st_ref_get(v___y_627_);
v_env_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc_ref(v_env_630_);
lean_dec(v___x_629_);
v___x_631_ = lean_st_ref_get(v___y_625_);
v_toCold_632_ = lean_ctor_get(v___y_626_, 0);
v_mctx_633_ = lean_ctor_get(v___x_631_, 0);
lean_inc_ref(v_mctx_633_);
lean_dec(v___x_631_);
v_lctx_634_ = lean_ctor_get(v___y_624_, 2);
v_options_635_ = lean_ctor_get(v_toCold_632_, 2);
lean_inc_ref(v_options_635_);
lean_inc_ref(v_lctx_634_);
v___x_636_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_636_, 0, v_env_630_);
lean_ctor_set(v___x_636_, 1, v_mctx_633_);
lean_ctor_set(v___x_636_, 2, v_lctx_634_);
lean_ctor_set(v___x_636_, 3, v_options_635_);
v___x_637_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v_msgData_623_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5___boxed(lean_object* v_msgData_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msgData_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(lean_object* v_msg_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_ref_652_; lean_object* v___x_653_; lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_662_; 
v_ref_652_ = lean_ctor_get(v___y_649_, 2);
v___x_653_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msg_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_662_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_662_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_662_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_660_; 
lean_inc(v_ref_652_);
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v_ref_652_);
lean_ctor_set(v___x_658_, 1, v_a_654_);
if (v_isShared_657_ == 0)
{
lean_ctor_set_tag(v___x_656_, 1);
lean_ctor_set(v___x_656_, 0, v___x_658_);
v___x_660_ = v___x_656_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg___boxed(lean_object* v_msg_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__0(lean_object* v_data_670_, lean_object* v_expr_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_Expr_mdata___override(v_data_670_, v_expr_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__1(lean_object* v_typeName_673_, lean_object* v_idx_674_, lean_object* v_struct_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Expr_proj___override(v_typeName_673_, v_idx_674_, v_struct_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(lean_object* v_a_677_, lean_object* v_b_678_, lean_object* v_x_679_){
_start:
{
if (lean_obj_tag(v_x_679_) == 0)
{
lean_dec(v_b_678_);
lean_dec(v_a_677_);
return v_x_679_;
}
else
{
lean_object* v_key_680_; lean_object* v_value_681_; lean_object* v_tail_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_694_; 
v_key_680_ = lean_ctor_get(v_x_679_, 0);
v_value_681_ = lean_ctor_get(v_x_679_, 1);
v_tail_682_ = lean_ctor_get(v_x_679_, 2);
v_isSharedCheck_694_ = !lean_is_exclusive(v_x_679_);
if (v_isSharedCheck_694_ == 0)
{
v___x_684_ = v_x_679_;
v_isShared_685_ = v_isSharedCheck_694_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_tail_682_);
lean_inc(v_value_681_);
lean_inc(v_key_680_);
lean_dec(v_x_679_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_694_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
uint8_t v___x_686_; 
v___x_686_ = l_Lean_instBEqFVarId_beq(v_key_680_, v_a_677_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_687_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_677_, v_b_678_, v_tail_682_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 2, v___x_687_);
v___x_689_ = v___x_684_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_key_680_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_value_681_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
else
{
lean_object* v___x_692_; 
lean_dec(v_value_681_);
lean_dec(v_key_680_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 1, v_b_678_);
lean_ctor_set(v___x_684_, 0, v_a_677_);
v___x_692_ = v___x_684_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_677_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_b_678_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_tail_682_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(lean_object* v_m_695_, lean_object* v_a_696_, lean_object* v_b_697_){
_start:
{
lean_object* v_size_698_; lean_object* v_buckets_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_742_; 
v_size_698_ = lean_ctor_get(v_m_695_, 0);
v_buckets_699_ = lean_ctor_get(v_m_695_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_m_695_);
if (v_isSharedCheck_742_ == 0)
{
v___x_701_ = v_m_695_;
v_isShared_702_ = v_isSharedCheck_742_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_buckets_699_);
lean_inc(v_size_698_);
lean_dec(v_m_695_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_742_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; uint64_t v___x_704_; uint64_t v___x_705_; uint64_t v___x_706_; uint64_t v_fold_707_; uint64_t v___x_708_; uint64_t v___x_709_; uint64_t v___x_710_; size_t v___x_711_; size_t v___x_712_; size_t v___x_713_; size_t v___x_714_; size_t v___x_715_; lean_object* v_bkt_716_; uint8_t v___x_717_; 
v___x_703_ = lean_array_get_size(v_buckets_699_);
v___x_704_ = l_Lean_instHashableFVarId_hash(v_a_696_);
v___x_705_ = 32ULL;
v___x_706_ = lean_uint64_shift_right(v___x_704_, v___x_705_);
v_fold_707_ = lean_uint64_xor(v___x_704_, v___x_706_);
v___x_708_ = 16ULL;
v___x_709_ = lean_uint64_shift_right(v_fold_707_, v___x_708_);
v___x_710_ = lean_uint64_xor(v_fold_707_, v___x_709_);
v___x_711_ = lean_uint64_to_usize(v___x_710_);
v___x_712_ = lean_usize_of_nat(v___x_703_);
v___x_713_ = ((size_t)1ULL);
v___x_714_ = lean_usize_sub(v___x_712_, v___x_713_);
v___x_715_ = lean_usize_land(v___x_711_, v___x_714_);
v_bkt_716_ = lean_array_uget_borrowed(v_buckets_699_, v___x_715_);
v___x_717_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_696_, v_bkt_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v_size_x27_719_; lean_object* v___x_720_; lean_object* v_buckets_x27_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_718_ = lean_unsigned_to_nat(1u);
v_size_x27_719_ = lean_nat_add(v_size_698_, v___x_718_);
lean_dec(v_size_698_);
lean_inc(v_bkt_716_);
v___x_720_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_720_, 0, v_a_696_);
lean_ctor_set(v___x_720_, 1, v_b_697_);
lean_ctor_set(v___x_720_, 2, v_bkt_716_);
v_buckets_x27_721_ = lean_array_uset(v_buckets_699_, v___x_715_, v___x_720_);
v___x_722_ = lean_unsigned_to_nat(4u);
v___x_723_ = lean_nat_mul(v_size_x27_719_, v___x_722_);
v___x_724_ = lean_unsigned_to_nat(3u);
v___x_725_ = lean_nat_div(v___x_723_, v___x_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_array_get_size(v_buckets_x27_721_);
v___x_727_ = lean_nat_dec_le(v___x_725_, v___x_726_);
lean_dec(v___x_725_);
if (v___x_727_ == 0)
{
lean_object* v_val_728_; lean_object* v___x_730_; 
v_val_728_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_721_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v_val_728_);
lean_ctor_set(v___x_701_, 0, v_size_x27_719_);
v___x_730_ = v___x_701_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_size_x27_719_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_val_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
else
{
lean_object* v___x_733_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v_buckets_x27_721_);
lean_ctor_set(v___x_701_, 0, v_size_x27_719_);
v___x_733_ = v___x_701_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_size_x27_719_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_buckets_x27_721_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
else
{
lean_object* v___x_735_; lean_object* v_buckets_x27_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
lean_inc(v_bkt_716_);
v___x_735_ = lean_box(0);
v_buckets_x27_736_ = lean_array_uset(v_buckets_699_, v___x_715_, v___x_735_);
v___x_737_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_696_, v_b_697_, v_bkt_716_);
v___x_738_ = lean_array_uset(v_buckets_x27_736_, v___x_715_, v___x_737_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_738_);
v___x_740_ = v___x_701_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_size_698_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(lean_object* v___y_743_){
_start:
{
lean_object* v___x_745_; lean_object* v_ngen_746_; lean_object* v_namePrefix_747_; lean_object* v_idx_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_778_; 
v___x_745_ = lean_st_ref_get(v___y_743_);
v_ngen_746_ = lean_ctor_get(v___x_745_, 2);
lean_inc_ref(v_ngen_746_);
lean_dec(v___x_745_);
v_namePrefix_747_ = lean_ctor_get(v_ngen_746_, 0);
v_idx_748_ = lean_ctor_get(v_ngen_746_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_ngen_746_);
if (v_isSharedCheck_778_ == 0)
{
v___x_750_ = v_ngen_746_;
v_isShared_751_ = v_isSharedCheck_778_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_idx_748_);
lean_inc(v_namePrefix_747_);
lean_dec(v_ngen_746_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_778_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v_r_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
lean_inc(v_idx_748_);
lean_inc(v_namePrefix_747_);
v_r_752_ = l_Lean_Name_num___override(v_namePrefix_747_, v_idx_748_);
v___x_753_ = lean_unsigned_to_nat(1u);
v___x_754_ = lean_nat_add(v_idx_748_, v___x_753_);
lean_dec(v_idx_748_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 1, v___x_754_);
v___x_756_ = v___x_750_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_namePrefix_747_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v___x_754_);
v___x_756_ = v_reuseFailAlloc_777_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v_env_758_; lean_object* v_nextMacroScope_759_; lean_object* v_auxDeclNGen_760_; lean_object* v_traceState_761_; lean_object* v_cache_762_; lean_object* v_recordedDeps_763_; lean_object* v_messages_764_; lean_object* v_infoState_765_; lean_object* v_snapshotTasks_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_775_; 
v___x_757_ = lean_st_ref_take(v___y_743_);
v_env_758_ = lean_ctor_get(v___x_757_, 0);
v_nextMacroScope_759_ = lean_ctor_get(v___x_757_, 1);
v_auxDeclNGen_760_ = lean_ctor_get(v___x_757_, 3);
v_traceState_761_ = lean_ctor_get(v___x_757_, 4);
v_cache_762_ = lean_ctor_get(v___x_757_, 5);
v_recordedDeps_763_ = lean_ctor_get(v___x_757_, 6);
v_messages_764_ = lean_ctor_get(v___x_757_, 7);
v_infoState_765_ = lean_ctor_get(v___x_757_, 8);
v_snapshotTasks_766_ = lean_ctor_get(v___x_757_, 9);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; 
v_unused_776_ = lean_ctor_get(v___x_757_, 2);
lean_dec(v_unused_776_);
v___x_768_ = v___x_757_;
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_snapshotTasks_766_);
lean_inc(v_infoState_765_);
lean_inc(v_messages_764_);
lean_inc(v_recordedDeps_763_);
lean_inc(v_cache_762_);
lean_inc(v_traceState_761_);
lean_inc(v_auxDeclNGen_760_);
lean_inc(v_nextMacroScope_759_);
lean_inc(v_env_758_);
lean_dec(v___x_757_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 2, v___x_756_);
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_env_758_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_nextMacroScope_759_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_auxDeclNGen_760_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v_traceState_761_);
lean_ctor_set(v_reuseFailAlloc_774_, 5, v_cache_762_);
lean_ctor_set(v_reuseFailAlloc_774_, 6, v_recordedDeps_763_);
lean_ctor_set(v_reuseFailAlloc_774_, 7, v_messages_764_);
lean_ctor_set(v_reuseFailAlloc_774_, 8, v_infoState_765_);
lean_ctor_set(v_reuseFailAlloc_774_, 9, v_snapshotTasks_766_);
v___x_771_ = v_reuseFailAlloc_774_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_st_ref_put(v___y_743_, v___x_771_);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v_r_752_);
return v___x_773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg___boxed(lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_779_);
lean_dec(v___y_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
v___x_787_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_785_);
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5___boxed(lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(lean_object* v_a_802_, lean_object* v_x_803_){
_start:
{
if (lean_obj_tag(v_x_803_) == 0)
{
return v_x_803_;
}
else
{
lean_object* v_key_804_; lean_object* v_value_805_; lean_object* v_tail_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_815_; 
v_key_804_ = lean_ctor_get(v_x_803_, 0);
v_value_805_ = lean_ctor_get(v_x_803_, 1);
v_tail_806_ = lean_ctor_get(v_x_803_, 2);
v_isSharedCheck_815_ = !lean_is_exclusive(v_x_803_);
if (v_isSharedCheck_815_ == 0)
{
v___x_808_ = v_x_803_;
v_isShared_809_ = v_isSharedCheck_815_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_tail_806_);
lean_inc(v_value_805_);
lean_inc(v_key_804_);
lean_dec(v_x_803_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_815_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
uint8_t v___x_810_; 
v___x_810_ = l_Lean_instBEqFVarId_beq(v_key_804_, v_a_802_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_811_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_802_, v_tail_806_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 2, v___x_811_);
v___x_813_ = v___x_808_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_key_804_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_value_805_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
else
{
lean_del_object(v___x_808_);
lean_dec(v_value_805_);
lean_dec(v_key_804_);
return v_tail_806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(lean_object* v_a_816_, lean_object* v_x_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_816_, v_x_817_);
lean_dec(v_a_816_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(lean_object* v_m_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_size_821_; lean_object* v_buckets_822_; lean_object* v___x_823_; uint64_t v___x_824_; uint64_t v___x_825_; uint64_t v___x_826_; uint64_t v_fold_827_; uint64_t v___x_828_; uint64_t v___x_829_; uint64_t v___x_830_; size_t v___x_831_; size_t v___x_832_; size_t v___x_833_; size_t v___x_834_; size_t v___x_835_; lean_object* v_bkt_836_; uint8_t v___x_837_; 
v_size_821_ = lean_ctor_get(v_m_819_, 0);
v_buckets_822_ = lean_ctor_get(v_m_819_, 1);
v___x_823_ = lean_array_get_size(v_buckets_822_);
v___x_824_ = l_Lean_instHashableFVarId_hash(v_a_820_);
v___x_825_ = 32ULL;
v___x_826_ = lean_uint64_shift_right(v___x_824_, v___x_825_);
v_fold_827_ = lean_uint64_xor(v___x_824_, v___x_826_);
v___x_828_ = 16ULL;
v___x_829_ = lean_uint64_shift_right(v_fold_827_, v___x_828_);
v___x_830_ = lean_uint64_xor(v_fold_827_, v___x_829_);
v___x_831_ = lean_uint64_to_usize(v___x_830_);
v___x_832_ = lean_usize_of_nat(v___x_823_);
v___x_833_ = ((size_t)1ULL);
v___x_834_ = lean_usize_sub(v___x_832_, v___x_833_);
v___x_835_ = lean_usize_land(v___x_831_, v___x_834_);
v_bkt_836_ = lean_array_uget_borrowed(v_buckets_822_, v___x_835_);
v___x_837_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_820_, v_bkt_836_);
if (v___x_837_ == 0)
{
return v_m_819_;
}
else
{
lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_850_; 
lean_inc(v_bkt_836_);
lean_inc_ref(v_buckets_822_);
lean_inc(v_size_821_);
v_isSharedCheck_850_ = !lean_is_exclusive(v_m_819_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; lean_object* v_unused_852_; 
v_unused_851_ = lean_ctor_get(v_m_819_, 1);
lean_dec(v_unused_851_);
v_unused_852_ = lean_ctor_get(v_m_819_, 0);
lean_dec(v_unused_852_);
v___x_839_ = v_m_819_;
v_isShared_840_ = v_isSharedCheck_850_;
goto v_resetjp_838_;
}
else
{
lean_dec(v_m_819_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_850_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v_buckets_x27_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_841_ = lean_box(0);
v_buckets_x27_842_ = lean_array_uset(v_buckets_822_, v___x_835_, v___x_841_);
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_nat_sub(v_size_821_, v___x_843_);
lean_dec(v_size_821_);
v___x_845_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_820_, v_bkt_836_);
v___x_846_ = lean_array_uset(v_buckets_x27_842_, v___x_835_, v___x_845_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v___x_846_);
lean_ctor_set(v___x_839_, 0, v___x_844_);
v___x_848_ = v___x_839_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v___x_846_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(lean_object* v_m_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_853_, v_a_854_);
lean_dec(v_a_854_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(lean_object* v_a_856_, lean_object* v_fallback_857_, lean_object* v_x_858_){
_start:
{
if (lean_obj_tag(v_x_858_) == 0)
{
lean_inc(v_fallback_857_);
return v_fallback_857_;
}
else
{
lean_object* v_key_859_; lean_object* v_value_860_; lean_object* v_tail_861_; uint8_t v___x_862_; 
v_key_859_ = lean_ctor_get(v_x_858_, 0);
v_value_860_ = lean_ctor_get(v_x_858_, 1);
v_tail_861_ = lean_ctor_get(v_x_858_, 2);
v___x_862_ = l_Lean_instBEqFVarId_beq(v_key_859_, v_a_856_);
if (v___x_862_ == 0)
{
v_x_858_ = v_tail_861_;
goto _start;
}
else
{
lean_inc(v_value_860_);
return v_value_860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(lean_object* v_a_864_, lean_object* v_fallback_865_, lean_object* v_x_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_864_, v_fallback_865_, v_x_866_);
lean_dec(v_x_866_);
lean_dec(v_fallback_865_);
lean_dec(v_a_864_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(lean_object* v_m_868_, lean_object* v_a_869_, lean_object* v_fallback_870_){
_start:
{
lean_object* v_buckets_871_; lean_object* v___x_872_; uint64_t v___x_873_; uint64_t v___x_874_; uint64_t v___x_875_; uint64_t v_fold_876_; uint64_t v___x_877_; uint64_t v___x_878_; uint64_t v___x_879_; size_t v___x_880_; size_t v___x_881_; size_t v___x_882_; size_t v___x_883_; size_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_buckets_871_ = lean_ctor_get(v_m_868_, 1);
v___x_872_ = lean_array_get_size(v_buckets_871_);
v___x_873_ = l_Lean_instHashableFVarId_hash(v_a_869_);
v___x_874_ = 32ULL;
v___x_875_ = lean_uint64_shift_right(v___x_873_, v___x_874_);
v_fold_876_ = lean_uint64_xor(v___x_873_, v___x_875_);
v___x_877_ = 16ULL;
v___x_878_ = lean_uint64_shift_right(v_fold_876_, v___x_877_);
v___x_879_ = lean_uint64_xor(v_fold_876_, v___x_878_);
v___x_880_ = lean_uint64_to_usize(v___x_879_);
v___x_881_ = lean_usize_of_nat(v___x_872_);
v___x_882_ = ((size_t)1ULL);
v___x_883_ = lean_usize_sub(v___x_881_, v___x_882_);
v___x_884_ = lean_usize_land(v___x_880_, v___x_883_);
v___x_885_ = lean_array_uget_borrowed(v_buckets_871_, v___x_884_);
v___x_886_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_869_, v_fallback_870_, v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(lean_object* v_m_887_, lean_object* v_a_888_, lean_object* v_fallback_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_887_, v_a_888_, v_fallback_889_);
lean_dec(v_fallback_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_m_887_);
return v_res_890_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = lean_box(0);
v___x_896_ = lean_unsigned_to_nat(16u);
v___x_897_ = lean_mk_array(v___x_896_, v___x_895_);
return v___x_897_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_899_ = lean_unsigned_to_nat(0u);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v___x_898_);
return v___x_900_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__1(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__0));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__3(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__2));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__5(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__4));
v___x_909_ = l_Lean_stringToMessageData(v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses(lean_object* v_e_910_, lean_object* v_subst_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
switch(lean_obj_tag(v_e_910_))
{
case 0:
{
lean_object* v_deBruijnIndex_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_deBruijnIndex_917_ = lean_ctor_get(v_e_910_, 0);
v___x_918_ = lean_array_get_size(v_subst_911_);
v___x_919_ = lean_nat_dec_lt(v_deBruijnIndex_917_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
lean_inc(v_deBruijnIndex_917_);
lean_dec_ref_known(v_e_910_, 1);
lean_dec_ref(v_subst_911_);
v___x_920_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__1, &l_Lean_Elab_Tactic_Do_countUses___closed__1_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__1);
v___x_921_ = l_Nat_reprFast(v_deBruijnIndex_917_);
v___x_922_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
v___x_923_ = l_Lean_MessageData_ofFormat(v___x_922_);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_920_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__3, &l_Lean_Elab_Tactic_Do_countUses___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__3);
v___x_926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = l_Nat_reprFast(v___x_918_);
v___x_928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
v___x_929_ = l_Lean_MessageData_ofFormat(v___x_928_);
v___x_930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_926_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_930_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
return v___x_931_;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_932_ = lean_unsigned_to_nat(1u);
v___x_933_ = lean_nat_sub(v___x_918_, v___x_932_);
v___x_934_ = lean_nat_sub(v___x_933_, v_deBruijnIndex_917_);
lean_dec(v___x_933_);
v___x_935_ = lean_array_fget(v_subst_911_, v___x_934_);
lean_dec(v___x_934_);
lean_dec_ref(v_subst_911_);
v___x_936_ = 1;
v___x_937_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_938_ = lean_box(v___x_936_);
v___x_939_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_937_, v___x_935_, v___x_938_);
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v_e_910_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
case 1:
{
lean_object* v_fvarId_942_; uint8_t v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
lean_dec_ref(v_subst_911_);
v_fvarId_942_ = lean_ctor_get(v_e_910_, 0);
v___x_943_ = 1;
v___x_944_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_945_ = lean_box(v___x_943_);
lean_inc(v_fvarId_942_);
v___x_946_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_944_, v_fvarId_942_, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v_e_910_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
case 5:
{
lean_object* v_fn_949_; lean_object* v_arg_950_; lean_object* v___x_951_; 
v_fn_949_ = lean_ctor_get(v_e_910_, 0);
lean_inc_ref(v_fn_949_);
v_arg_950_ = lean_ctor_get(v_e_910_, 1);
lean_inc_ref(v_arg_950_);
lean_dec_ref_known(v_e_910_, 2);
lean_inc_ref(v_subst_911_);
v___x_951_ = l_Lean_Elab_Tactic_Do_countUses(v_fn_949_, v_subst_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v_fst_953_; lean_object* v_snd_954_; lean_object* v___x_955_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v_fst_953_ = lean_ctor_get(v_a_952_, 0);
lean_inc(v_fst_953_);
v_snd_954_ = lean_ctor_get(v_a_952_, 1);
lean_inc(v_snd_954_);
lean_dec(v_a_952_);
v___x_955_ = l_Lean_Elab_Tactic_Do_countUses(v_arg_950_, v_subst_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_974_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_974_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_974_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_974_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_fst_960_; lean_object* v_snd_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_973_; 
v_fst_960_ = lean_ctor_get(v_a_956_, 0);
v_snd_961_ = lean_ctor_get(v_a_956_, 1);
v_isSharedCheck_973_ = !lean_is_exclusive(v_a_956_);
if (v_isSharedCheck_973_ == 0)
{
v___x_963_ = v_a_956_;
v_isShared_964_ = v_isSharedCheck_973_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_snd_961_);
lean_inc(v_fst_960_);
lean_dec(v_a_956_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_973_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_965_ = l_Lean_Expr_app___override(v_fst_953_, v_fst_960_);
v___x_966_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_954_, v_snd_961_);
lean_dec(v_snd_954_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 1, v___x_966_);
lean_ctor_set(v___x_963_, 0, v___x_965_);
v___x_968_ = v___x_963_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_966_);
v___x_968_ = v_reuseFailAlloc_972_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_970_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_968_);
v___x_970_ = v___x_958_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
else
{
lean_dec(v_snd_954_);
lean_dec(v_fst_953_);
return v___x_955_;
}
}
else
{
lean_dec_ref(v_arg_950_);
lean_dec_ref(v_subst_911_);
return v___x_951_;
}
}
case 6:
{
lean_object* v_binderName_975_; lean_object* v_binderType_976_; lean_object* v_body_977_; uint8_t v_binderInfo_978_; lean_object* v___x_979_; 
v_binderName_975_ = lean_ctor_get(v_e_910_, 0);
lean_inc(v_binderName_975_);
v_binderType_976_ = lean_ctor_get(v_e_910_, 1);
lean_inc_ref(v_binderType_976_);
v_body_977_ = lean_ctor_get(v_e_910_, 2);
lean_inc_ref(v_body_977_);
v_binderInfo_978_ = lean_ctor_get_uint8(v_e_910_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_910_, 3);
v___x_979_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
lean_inc_ref(v_subst_911_);
v___x_981_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_976_, v_subst_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v_fst_983_; lean_object* v_snd_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
v_fst_983_ = lean_ctor_get(v_a_982_, 0);
lean_inc(v_fst_983_);
v_snd_984_ = lean_ctor_get(v_a_982_, 1);
lean_inc(v_snd_984_);
lean_dec(v_a_982_);
lean_inc(v_a_980_);
v___x_985_ = lean_array_push(v_subst_911_, v_a_980_);
v___x_986_ = l_Lean_Elab_Tactic_Do_countUses(v_body_977_, v___x_985_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1006_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_1006_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1006_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v_fst_991_; lean_object* v_snd_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1005_; 
v_fst_991_ = lean_ctor_get(v_a_987_, 0);
v_snd_992_ = lean_ctor_get(v_a_987_, 1);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_a_987_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_994_ = v_a_987_;
v_isShared_995_ = v_isSharedCheck_1005_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_snd_992_);
lean_inc(v_fst_991_);
lean_dec(v_a_987_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1005_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_996_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_984_, v_snd_992_);
lean_dec(v_snd_984_);
v___x_997_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_996_, v_a_980_);
lean_dec(v_a_980_);
v___x_998_ = l_Lean_Expr_lam___override(v_binderName_975_, v_fst_983_, v_fst_991_, v_binderInfo_978_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v___x_997_);
lean_ctor_set(v___x_994_, 0, v___x_998_);
v___x_1000_ = v___x_994_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v___x_997_);
v___x_1000_ = v_reuseFailAlloc_1004_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1002_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_1000_);
v___x_1002_ = v___x_989_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
else
{
lean_dec(v_snd_984_);
lean_dec(v_fst_983_);
lean_dec(v_a_980_);
lean_dec(v_binderName_975_);
return v___x_986_;
}
}
else
{
lean_dec(v_a_980_);
lean_dec_ref(v_body_977_);
lean_dec(v_binderName_975_);
lean_dec_ref(v_subst_911_);
return v___x_981_;
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v_body_977_);
lean_dec_ref(v_binderType_976_);
lean_dec(v_binderName_975_);
lean_dec_ref(v_subst_911_);
v_a_1007_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_979_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_979_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1015_; lean_object* v_binderType_1016_; lean_object* v_body_1017_; uint8_t v_binderInfo_1018_; lean_object* v___x_1019_; 
v_binderName_1015_ = lean_ctor_get(v_e_910_, 0);
lean_inc(v_binderName_1015_);
v_binderType_1016_ = lean_ctor_get(v_e_910_, 1);
lean_inc_ref(v_binderType_1016_);
v_body_1017_ = lean_ctor_get(v_e_910_, 2);
lean_inc_ref(v_body_1017_);
v_binderInfo_1018_ = lean_ctor_get_uint8(v_e_910_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_910_, 3);
v___x_1019_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1021_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
lean_inc_ref(v_subst_911_);
v___x_1021_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_1016_, v_subst_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v_fst_1023_; lean_object* v_snd_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v_fst_1023_ = lean_ctor_get(v_a_1022_, 0);
lean_inc(v_fst_1023_);
v_snd_1024_ = lean_ctor_get(v_a_1022_, 1);
lean_inc(v_snd_1024_);
lean_dec(v_a_1022_);
lean_inc(v_a_1020_);
v___x_1025_ = lean_array_push(v_subst_911_, v_a_1020_);
v___x_1026_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1017_, v___x_1025_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1046_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1046_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1046_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_fst_1031_; lean_object* v_snd_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1045_; 
v_fst_1031_ = lean_ctor_get(v_a_1027_, 0);
v_snd_1032_ = lean_ctor_get(v_a_1027_, 1);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_a_1027_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1034_ = v_a_1027_;
v_isShared_1035_ = v_isSharedCheck_1045_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_snd_1032_);
lean_inc(v_fst_1031_);
lean_dec(v_a_1027_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1045_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1036_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_1024_, v_snd_1032_);
lean_dec(v_snd_1024_);
v___x_1037_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_1036_, v_a_1020_);
lean_dec(v_a_1020_);
v___x_1038_ = l_Lean_Expr_forallE___override(v_binderName_1015_, v_fst_1023_, v_fst_1031_, v_binderInfo_1018_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v___x_1037_);
lean_ctor_set(v___x_1034_, 0, v___x_1038_);
v___x_1040_ = v___x_1034_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1037_);
v___x_1040_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1042_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1040_);
v___x_1042_ = v___x_1029_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
else
{
lean_dec(v_snd_1024_);
lean_dec(v_fst_1023_);
lean_dec(v_a_1020_);
lean_dec(v_binderName_1015_);
return v___x_1026_;
}
}
else
{
lean_dec(v_a_1020_);
lean_dec_ref(v_body_1017_);
lean_dec(v_binderName_1015_);
lean_dec_ref(v_subst_911_);
return v___x_1021_;
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec_ref(v_body_1017_);
lean_dec_ref(v_binderType_1016_);
lean_dec(v_binderName_1015_);
lean_dec_ref(v_subst_911_);
v_a_1047_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1019_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1019_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
case 8:
{
lean_object* v_declName_1055_; lean_object* v_type_1056_; lean_object* v_value_1057_; lean_object* v_body_1058_; uint8_t v_nondep_1059_; lean_object* v___x_1060_; 
v_declName_1055_ = lean_ctor_get(v_e_910_, 0);
lean_inc(v_declName_1055_);
v_type_1056_ = lean_ctor_get(v_e_910_, 1);
lean_inc_ref(v_type_1056_);
v_value_1057_ = lean_ctor_get(v_e_910_, 2);
lean_inc_ref(v_value_1057_);
v_body_1058_ = lean_ctor_get(v_e_910_, 3);
lean_inc_ref(v_body_1058_);
v_nondep_1059_ = lean_ctor_get_uint8(v_e_910_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_910_, 4);
v___x_1060_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc_n(v_a_1061_, 2);
lean_dec_ref_known(v___x_1060_, 1);
lean_inc_ref(v_subst_911_);
v___x_1062_ = lean_array_push(v_subst_911_, v_a_1061_);
v___x_1063_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1058_, v___x_1062_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1106_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1106_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1106_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_fst_1068_; lean_object* v_snd_1069_; lean_object* v___x_1071_; 
v_fst_1068_ = lean_ctor_get(v_a_1064_, 0);
lean_inc(v_fst_1068_);
v_snd_1069_ = lean_ctor_get(v_a_1064_, 1);
lean_inc(v_snd_1069_);
lean_dec(v_a_1064_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 1);
lean_ctor_set(v___x_1066_, 0, v_value_1057_);
v___x_1071_ = v___x_1066_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_value_1057_);
v___x_1071_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_a_1061_, v_type_1056_, v___x_1071_, v_snd_1069_, v_subst_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
lean_dec(v_a_1061_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1096_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1096_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1096_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v_snd_1077_; lean_object* v_fst_1078_; 
v_snd_1077_ = lean_ctor_get(v_a_1073_, 1);
lean_inc(v_snd_1077_);
v_fst_1078_ = lean_ctor_get(v_snd_1077_, 0);
lean_inc(v_fst_1078_);
if (lean_obj_tag(v_fst_1078_) == 1)
{
lean_object* v_fst_1079_; lean_object* v_snd_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1092_; 
v_fst_1079_ = lean_ctor_get(v_a_1073_, 0);
lean_inc(v_fst_1079_);
lean_dec(v_a_1073_);
v_snd_1080_ = lean_ctor_get(v_snd_1077_, 1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_snd_1077_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; 
v_unused_1093_ = lean_ctor_get(v_snd_1077_, 0);
lean_dec(v_unused_1093_);
v___x_1082_ = v_snd_1077_;
v_isShared_1083_ = v_isSharedCheck_1092_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_snd_1080_);
lean_dec(v_snd_1077_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1092_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v_val_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v_val_1084_ = lean_ctor_get(v_fst_1078_, 0);
lean_inc(v_val_1084_);
lean_dec_ref_known(v_fst_1078_, 1);
v___x_1085_ = l_Lean_Expr_letE___override(v_declName_1055_, v_fst_1079_, v_val_1084_, v_fst_1068_, v_nondep_1059_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1085_);
v___x_1087_ = v___x_1082_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_snd_1080_);
v___x_1087_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1089_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1087_);
v___x_1089_ = v___x_1075_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
else
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_dec(v_fst_1078_);
lean_dec(v_snd_1077_);
lean_del_object(v___x_1075_);
lean_dec(v_a_1073_);
lean_dec(v_fst_1068_);
lean_dec(v_declName_1055_);
v___x_1094_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__5, &l_Lean_Elab_Tactic_Do_countUses___closed__5_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__5);
v___x_1095_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_1094_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
return v___x_1095_;
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec(v_fst_1068_);
lean_dec(v_declName_1055_);
v_a_1097_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1072_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1072_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1061_);
lean_dec_ref(v_value_1057_);
lean_dec_ref(v_type_1056_);
lean_dec(v_declName_1055_);
lean_dec_ref(v_subst_911_);
return v___x_1063_;
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec_ref(v_body_1058_);
lean_dec_ref(v_value_1057_);
lean_dec_ref(v_type_1056_);
lean_dec(v_declName_1055_);
lean_dec_ref(v_subst_911_);
v_a_1107_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1060_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1060_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
case 10:
{
lean_object* v_data_1115_; lean_object* v_expr_1116_; lean_object* v___f_1117_; lean_object* v___x_1118_; 
v_data_1115_ = lean_ctor_get(v_e_910_, 0);
lean_inc(v_data_1115_);
v_expr_1116_ = lean_ctor_get(v_e_910_, 1);
lean_inc_ref(v_expr_1116_);
lean_dec_ref_known(v_e_910_, 2);
v___f_1117_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__0), 2, 1);
lean_closure_set(v___f_1117_, 0, v_data_1115_);
v___x_1118_ = l_Lean_Elab_Tactic_Do_countUses(v_expr_1116_, v_subst_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1127_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1123_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1117_, v_a_1119_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1123_);
v___x_1125_ = v___x_1121_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
else
{
lean_dec_ref(v___f_1117_);
return v___x_1118_;
}
}
case 11:
{
lean_object* v_typeName_1128_; lean_object* v_idx_1129_; lean_object* v_struct_1130_; lean_object* v___f_1131_; lean_object* v___x_1132_; 
v_typeName_1128_ = lean_ctor_get(v_e_910_, 0);
lean_inc(v_typeName_1128_);
v_idx_1129_ = lean_ctor_get(v_e_910_, 1);
lean_inc(v_idx_1129_);
v_struct_1130_ = lean_ctor_get(v_e_910_, 2);
lean_inc_ref(v_struct_1130_);
lean_dec_ref_known(v_e_910_, 3);
v___f_1131_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__1), 3, 2);
lean_closure_set(v___f_1131_, 0, v_typeName_1128_);
lean_closure_set(v___f_1131_, 1, v_idx_1129_);
v___x_1132_ = l_Lean_Elab_Tactic_Do_countUses(v_struct_1130_, v_subst_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1131_, v_a_1133_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1137_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
else
{
lean_dec_ref(v___f_1131_);
return v___x_1132_;
}
}
default: 
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec_ref(v_subst_911_);
v___x_1142_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v_e_910_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl(lean_object* v_fvarId_1145_, lean_object* v_ty_1146_, lean_object* v_val_x3f_1147_, lean_object* v_bodyUses_1148_, lean_object* v_subst_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
lean_object* v___f_1155_; lean_object* v___x_1156_; 
v___f_1155_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0));
lean_inc_ref(v_subst_1149_);
v___x_1156_ = l_Lean_Elab_Tactic_Do_countUses(v_ty_1146_, v_subst_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1211_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1211_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1211_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_fst_1161_; lean_object* v_snd_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1210_; 
v_fst_1161_ = lean_ctor_get(v_a_1157_, 0);
v_snd_1162_ = lean_ctor_get(v_a_1157_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_a_1157_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1164_ = v_a_1157_;
v_isShared_1165_ = v_isSharedCheck_1210_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_snd_1162_);
lean_inc(v_fst_1161_);
lean_dec(v_a_1157_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1210_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___y_1167_; uint8_t v___y_1168_; lean_object* v___y_1169_; lean_object* v_fst_1184_; lean_object* v_snd_1185_; 
if (lean_obj_tag(v_val_x3f_1147_) == 0)
{
lean_object* v___x_1195_; 
lean_dec_ref(v_subst_1149_);
v___x_1195_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v_fst_1184_ = v_val_x3f_1147_;
v_snd_1185_ = v___x_1195_;
goto v___jp_1183_;
}
else
{
lean_object* v_val_1196_; lean_object* v___x_1197_; 
v_val_1196_ = lean_ctor_get(v_val_x3f_1147_, 0);
lean_inc(v_val_1196_);
lean_dec_ref_known(v_val_x3f_1147_, 1);
v___x_1197_ = l_Lean_Elab_Tactic_Do_countUses(v_val_1196_, v_subst_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1199_; lean_object* v_fst_1200_; lean_object* v_snd_1201_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1197_, 1);
v___x_1199_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1155_, v_a_1198_);
v_fst_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_fst_1200_);
v_snd_1201_ = lean_ctor_get(v___x_1199_, 1);
lean_inc(v_snd_1201_);
lean_dec_ref(v___x_1199_);
v_fst_1184_ = v_fst_1200_;
v_snd_1185_ = v_snd_1201_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_del_object(v___x_1164_);
lean_dec(v_snd_1162_);
lean_dec(v_fst_1161_);
lean_del_object(v___x_1159_);
lean_dec_ref(v_bodyUses_1148_);
v_a_1202_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1197_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1197_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
v___jp_1166_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1170_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___y_1169_, v_fvarId_1145_);
v___x_1171_ = lean_box(0);
v___x_1172_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_1173_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v___y_1168_);
v___x_1174_ = l_Lean_KVMap_setNat(v___x_1171_, v___x_1172_, v___x_1173_);
v___x_1175_ = l_Lean_Elab_Tactic_Do_addMData(v___x_1174_, v_fst_1161_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1170_);
lean_ctor_set(v___x_1164_, 0, v___y_1167_);
v___x_1177_ = v___x_1164_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___y_1167_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1170_);
v___x_1177_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1175_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1178_);
v___x_1180_ = v___x_1159_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
v___jp_1183_:
{
uint8_t v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; uint8_t v___x_1190_; 
v___x_1186_ = 0;
v___x_1187_ = lean_box(v___x_1186_);
v___x_1188_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_bodyUses_1148_, v_fvarId_1145_, v___x_1187_);
lean_dec(v___x_1187_);
v___x_1189_ = lean_unbox(v___x_1188_);
v___x_1190_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v___x_1189_, v___x_1186_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1191_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_bodyUses_1148_, v_snd_1162_);
lean_dec_ref(v_bodyUses_1148_);
v___x_1192_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v___x_1191_, v_snd_1185_);
lean_dec_ref(v___x_1191_);
v___x_1193_ = lean_unbox(v___x_1188_);
lean_dec(v___x_1188_);
v___y_1167_ = v_fst_1184_;
v___y_1168_ = v___x_1193_;
v___y_1169_ = v___x_1192_;
goto v___jp_1166_;
}
else
{
uint8_t v___x_1194_; 
lean_dec_ref(v_snd_1185_);
lean_dec(v_snd_1162_);
v___x_1194_ = lean_unbox(v___x_1188_);
lean_dec(v___x_1188_);
v___y_1167_ = v_fst_1184_;
v___y_1168_ = v___x_1194_;
v___y_1169_ = v_bodyUses_1148_;
goto v___jp_1166_;
}
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec_ref(v_subst_1149_);
lean_dec_ref(v_bodyUses_1148_);
lean_dec(v_val_x3f_1147_);
v_a_1212_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1156_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1156_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___boxed(lean_object* v_fvarId_1220_, lean_object* v_ty_1221_, lean_object* v_val_x3f_1222_, lean_object* v_bodyUses_1223_, lean_object* v_subst_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_fvarId_1220_, v_ty_1221_, v_val_x3f_1222_, v_bodyUses_1223_, v_subst_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_fvarId_1220_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___boxed(lean_object* v_e_1231_, lean_object* v_subst_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Elab_Tactic_Do_countUses(v_e_1231_, v_subst_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(lean_object* v_00_u03b2_1239_, lean_object* v_m_1240_, lean_object* v_a_1241_, lean_object* v_fallback_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_1240_, v_a_1241_, v_fallback_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(lean_object* v_00_u03b2_1244_, lean_object* v_m_1245_, lean_object* v_a_1246_, lean_object* v_fallback_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(v_00_u03b2_1244_, v_m_1245_, v_a_1246_, v_fallback_1247_);
lean_dec(v_fallback_1247_);
lean_dec(v_a_1246_);
lean_dec_ref(v_m_1245_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(lean_object* v_00_u03b2_1249_, lean_object* v_m_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_1250_, v_a_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(lean_object* v_00_u03b2_1253_, lean_object* v_m_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(v_00_u03b2_1253_, v_m_1254_, v_a_1255_);
lean_dec(v_a_1255_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(lean_object* v_00_u03b1_1257_, lean_object* v_msg_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___boxed(lean_object* v_00_u03b1_1265_, lean_object* v_msg_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(v_00_u03b1_1265_, v_msg_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4(lean_object* v_00_u03b2_1273_, lean_object* v_m_1274_, lean_object* v_a_1275_, lean_object* v_b_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v_m_1274_, v_a_1275_, v_b_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_1281_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___boxed(lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(lean_object* v_00_u03b2_1290_, lean_object* v_a_1291_, lean_object* v_fallback_1292_, lean_object* v_x_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_1291_, v_fallback_1292_, v_x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1295_, lean_object* v_a_1296_, lean_object* v_fallback_1297_, lean_object* v_x_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(v_00_u03b2_1295_, v_a_1296_, v_fallback_1297_, v_x_1298_);
lean_dec(v_x_1298_);
lean_dec(v_fallback_1297_);
lean_dec(v_a_1296_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(lean_object* v_00_u03b2_1300_, lean_object* v_a_1301_, lean_object* v_x_1302_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_1301_, v_x_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1304_, lean_object* v_a_1305_, lean_object* v_x_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(v_00_u03b2_1304_, v_a_1305_, v_x_1306_);
lean_dec(v_a_1305_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(lean_object* v_00_u03b2_1308_, lean_object* v_a_1309_, lean_object* v_b_1310_, lean_object* v_x_1311_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_1309_, v_b_1310_, v_x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(lean_object* v_as_1315_, size_t v_i_1316_, size_t v_stop_1317_, lean_object* v_b_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_usize_dec_eq(v_i_1316_, v_stop_1317_);
if (v___x_1324_ == 0)
{
size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = ((size_t)1ULL);
v___x_1326_ = lean_usize_sub(v_i_1316_, v___x_1325_);
v___x_1327_ = lean_array_uget_borrowed(v_as_1315_, v___x_1326_);
if (lean_obj_tag(v___x_1327_) == 0)
{
v_i_1316_ = v___x_1326_;
goto _start;
}
else
{
lean_object* v_val_1329_; lean_object* v_fst_1330_; lean_object* v_snd_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v_val_1329_ = lean_ctor_get(v___x_1327_, 0);
v_fst_1330_ = lean_ctor_get(v_b_1318_, 0);
lean_inc(v_fst_1330_);
v_snd_1331_ = lean_ctor_get(v_b_1318_, 1);
lean_inc(v_snd_1331_);
lean_dec_ref(v_b_1318_);
v___x_1332_ = l_Lean_LocalDecl_fvarId(v_val_1329_);
v___x_1333_ = l_Lean_LocalDecl_type(v_val_1329_);
v___x_1334_ = l_Lean_LocalDecl_value_x3f(v_val_1329_, v___x_1324_);
v___x_1335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_1336_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v___x_1332_, v___x_1333_, v___x_1334_, v_snd_1331_, v___x_1335_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___x_1332_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v_snd_1338_; lean_object* v_fst_1339_; lean_object* v_fst_1340_; lean_object* v_snd_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1356_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1336_, 1);
v_snd_1338_ = lean_ctor_get(v_a_1337_, 1);
lean_inc(v_snd_1338_);
v_fst_1339_ = lean_ctor_get(v_a_1337_, 0);
lean_inc(v_fst_1339_);
lean_dec(v_a_1337_);
v_fst_1340_ = lean_ctor_get(v_snd_1338_, 0);
v_snd_1341_ = lean_ctor_get(v_snd_1338_, 1);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_snd_1338_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1343_ = v_snd_1338_;
v_isShared_1344_ = v_isSharedCheck_1356_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_snd_1341_);
lean_inc(v_fst_1340_);
lean_dec(v_snd_1338_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1356_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___y_1346_; 
if (lean_obj_tag(v_fst_1340_) == 0)
{
lean_object* v___x_1352_; 
lean_inc(v_val_1329_);
v___x_1352_ = l_Lean_LocalDecl_setType(v_val_1329_, v_fst_1339_);
v___y_1346_ = v___x_1352_;
goto v___jp_1345_;
}
else
{
lean_object* v_val_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v_val_1353_ = lean_ctor_get(v_fst_1340_, 0);
lean_inc(v_val_1353_);
lean_dec_ref_known(v_fst_1340_, 1);
lean_inc(v_val_1329_);
v___x_1354_ = l_Lean_LocalDecl_setType(v_val_1329_, v_fst_1339_);
v___x_1355_ = l_Lean_LocalDecl_setValue(v___x_1354_, v_val_1353_);
v___y_1346_ = v___x_1355_;
goto v___jp_1345_;
}
v___jp_1345_:
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = lean_array_push(v_fst_1330_, v___y_1346_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1347_);
v___x_1349_ = v___x_1343_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_snd_1341_);
v___x_1349_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
v_i_1316_ = v___x_1326_;
v_b_1318_ = v___x_1349_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec(v_fst_1330_);
v_a_1357_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1336_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1336_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
else
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v_b_1318_);
return v___x_1365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1366_, lean_object* v_i_1367_, lean_object* v_stop_1368_, lean_object* v_b_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
size_t v_i_boxed_1375_; size_t v_stop_boxed_1376_; lean_object* v_res_1377_; 
v_i_boxed_1375_ = lean_unbox_usize(v_i_1367_);
lean_dec(v_i_1367_);
v_stop_boxed_1376_ = lean_unbox_usize(v_stop_1368_);
lean_dec(v_stop_1368_);
v_res_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_as_1366_, v_i_boxed_1375_, v_stop_boxed_1376_, v_b_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec_ref(v_as_1366_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(lean_object* v_x_1378_, lean_object* v_x_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
if (lean_obj_tag(v_x_1378_) == 0)
{
lean_object* v_cs_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1398_; 
v_cs_1385_ = lean_ctor_get(v_x_1378_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_x_1378_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1387_ = v_x_1378_;
v_isShared_1388_ = v_isSharedCheck_1398_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_cs_1385_);
lean_dec(v_x_1378_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1398_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1389_ = lean_array_get_size(v_cs_1385_);
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = lean_nat_dec_lt(v___x_1390_, v___x_1389_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1393_; 
lean_dec_ref(v_cs_1385_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v_x_1379_);
v___x_1393_ = v___x_1387_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_x_1379_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
else
{
size_t v___x_1395_; size_t v___x_1396_; lean_object* v___x_1397_; 
lean_del_object(v___x_1387_);
v___x_1395_ = lean_usize_of_nat(v___x_1389_);
v___x_1396_ = ((size_t)0ULL);
v___x_1397_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_cs_1385_, v___x_1395_, v___x_1396_, v_x_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec_ref(v_cs_1385_);
return v___x_1397_;
}
}
}
else
{
lean_object* v_vs_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1412_; 
v_vs_1399_ = lean_ctor_get(v_x_1378_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_x_1378_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1401_ = v_x_1378_;
v_isShared_1402_ = v_isSharedCheck_1412_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_vs_1399_);
lean_dec(v_x_1378_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1412_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1403_ = lean_array_get_size(v_vs_1399_);
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = lean_nat_dec_lt(v___x_1404_, v___x_1403_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1407_; 
lean_dec_ref(v_vs_1399_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set_tag(v___x_1401_, 0);
lean_ctor_set(v___x_1401_, 0, v_x_1379_);
v___x_1407_ = v___x_1401_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_x_1379_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
else
{
size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; 
lean_del_object(v___x_1401_);
v___x_1409_ = lean_usize_of_nat(v___x_1403_);
v___x_1410_ = ((size_t)0ULL);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_vs_1399_, v___x_1409_, v___x_1410_, v_x_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec_ref(v_vs_1399_);
return v___x_1411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_1413_, size_t v_i_1414_, size_t v_stop_1415_, lean_object* v_b_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
uint8_t v___x_1422_; 
v___x_1422_ = lean_usize_dec_eq(v_i_1414_, v_stop_1415_);
if (v___x_1422_ == 0)
{
size_t v___x_1423_; size_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1423_ = ((size_t)1ULL);
v___x_1424_ = lean_usize_sub(v_i_1414_, v___x_1423_);
v___x_1425_ = lean_array_uget_borrowed(v_as_1413_, v___x_1424_);
lean_inc(v___x_1425_);
v___x_1426_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v___x_1425_, v_b_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v_i_1414_ = v___x_1424_;
v_b_1416_ = v_a_1427_;
goto _start;
}
else
{
return v___x_1426_;
}
}
else
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1429_, 0, v_b_1416_);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_1430_, lean_object* v_i_1431_, lean_object* v_stop_1432_, lean_object* v_b_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
size_t v_i_boxed_1439_; size_t v_stop_boxed_1440_; lean_object* v_res_1441_; 
v_i_boxed_1439_ = lean_unbox_usize(v_i_1431_);
lean_dec(v_i_1431_);
v_stop_boxed_1440_ = lean_unbox_usize(v_stop_1432_);
lean_dec(v_stop_1432_);
v_res_1441_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_as_1430_, v_i_boxed_1439_, v_stop_boxed_1440_, v_b_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec_ref(v_as_1430_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1442_, lean_object* v_x_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_x_1442_, v_x_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(lean_object* v_t_1450_, lean_object* v_init_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_root_1457_; lean_object* v_tail_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v_root_1457_ = lean_ctor_get(v_t_1450_, 0);
lean_inc_ref(v_root_1457_);
v_tail_1458_ = lean_ctor_get(v_t_1450_, 1);
lean_inc_ref(v_tail_1458_);
lean_dec_ref(v_t_1450_);
v___x_1459_ = lean_array_get_size(v_tail_1458_);
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_nat_dec_lt(v___x_1460_, v___x_1459_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; 
lean_dec_ref(v_tail_1458_);
v___x_1462_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1457_, v_init_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
return v___x_1462_;
}
else
{
size_t v___x_1463_; size_t v___x_1464_; lean_object* v___x_1465_; 
v___x_1463_ = lean_usize_of_nat(v___x_1459_);
v___x_1464_ = ((size_t)0ULL);
v___x_1465_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_tail_1458_, v___x_1463_, v___x_1464_, v_init_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec_ref(v_tail_1458_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1467_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1465_, 1);
v___x_1467_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1457_, v_a_1466_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
return v___x_1467_;
}
else
{
lean_dec_ref(v_root_1457_);
return v___x_1465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(lean_object* v_t_1468_, lean_object* v_init_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_t_1468_, v_init_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(lean_object* v_lctx_1476_, lean_object* v_init_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_decls_1483_; lean_object* v___x_1484_; 
v_decls_1483_ = lean_ctor_get(v_lctx_1476_, 1);
lean_inc_ref(v_decls_1483_);
lean_dec_ref(v_lctx_1476_);
v___x_1484_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_decls_1483_, v_init_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(lean_object* v_lctx_1485_, lean_object* v_init_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_lctx_1485_, v_init_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(size_t v_sz_1493_, size_t v_i_1494_, lean_object* v_bs_1495_, lean_object* v___y_1496_){
_start:
{
uint8_t v___x_1498_; 
v___x_1498_ = lean_usize_dec_lt(v_i_1494_, v_sz_1493_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v_bs_1495_);
return v___x_1499_;
}
else
{
lean_object* v_v_1500_; lean_object* v___x_1501_; lean_object* v_bs_x27_1502_; lean_object* v_a_1504_; 
v_v_1500_ = lean_array_uget(v_bs_1495_, v_i_1494_);
v___x_1501_ = lean_unsigned_to_nat(0u);
v_bs_x27_1502_ = lean_array_uset(v_bs_1495_, v_i_1494_, v___x_1501_);
if (lean_obj_tag(v_v_1500_) == 0)
{
v_a_1504_ = v_v_1500_;
goto v___jp_1503_;
}
else
{
lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1523_; 
v_isSharedCheck_1523_ = !lean_is_exclusive(v_v_1500_);
if (v_isSharedCheck_1523_ == 0)
{
lean_object* v_unused_1524_; 
v_unused_1524_ = lean_ctor_get(v_v_1500_, 0);
lean_dec(v_unused_1524_);
v___x_1510_ = v_v_1500_;
v_isShared_1511_ = v_isSharedCheck_1523_;
goto v_resetjp_1509_;
}
else
{
lean_dec(v_v_1500_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1523_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1512_ = l_Lean_instInhabitedLocalDecl_default;
v___x_1513_ = lean_st_ref_take(v___y_1496_);
v___x_1514_ = lean_array_get_size(v___x_1513_);
v___x_1515_ = lean_unsigned_to_nat(1u);
v___x_1516_ = lean_nat_sub(v___x_1514_, v___x_1515_);
v___x_1517_ = lean_array_get(v___x_1512_, v___x_1513_, v___x_1516_);
lean_dec(v___x_1516_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1517_);
v___x_1519_ = v___x_1510_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = lean_array_pop(v___x_1513_);
v___x_1521_ = lean_st_ref_put(v___y_1496_, v___x_1520_);
v_a_1504_ = v___x_1519_;
goto v___jp_1503_;
}
}
}
v___jp_1503_:
{
size_t v___x_1505_; size_t v___x_1506_; lean_object* v___x_1507_; 
v___x_1505_ = ((size_t)1ULL);
v___x_1506_ = lean_usize_add(v_i_1494_, v___x_1505_);
v___x_1507_ = lean_array_uset(v_bs_x27_1502_, v_i_1494_, v_a_1504_);
v_i_1494_ = v___x_1506_;
v_bs_1495_ = v___x_1507_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg___boxed(lean_object* v_sz_1525_, lean_object* v_i_1526_, lean_object* v_bs_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
size_t v_sz_boxed_1530_; size_t v_i_boxed_1531_; lean_object* v_res_1532_; 
v_sz_boxed_1530_ = lean_unbox_usize(v_sz_1525_);
lean_dec(v_sz_1525_);
v_i_boxed_1531_ = lean_unbox_usize(v_i_1526_);
lean_dec(v_i_1526_);
v_res_1532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_boxed_1530_, v_i_boxed_1531_, v_bs_1527_, v___y_1528_);
lean_dec(v___y_1528_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(lean_object* v_x_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
if (lean_obj_tag(v_x_1533_) == 0)
{
lean_object* v_cs_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1566_; 
v_cs_1540_ = lean_ctor_get(v_x_1533_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_x_1533_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1542_ = v_x_1533_;
v_isShared_1543_ = v_isSharedCheck_1566_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_cs_1540_);
lean_dec(v_x_1533_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1566_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
size_t v_sz_1544_; size_t v___x_1545_; lean_object* v___x_1546_; 
v_sz_1544_ = lean_array_size(v_cs_1540_);
v___x_1545_ = ((size_t)0ULL);
v___x_1546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_1544_, v___x_1545_, v_cs_1540_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1557_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1557_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1557_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v_a_1547_);
v___x_1552_ = v___x_1542_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1554_; 
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1552_);
v___x_1554_ = v___x_1549_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_del_object(v___x_1542_);
v_a_1558_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1546_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1546_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
else
{
lean_object* v_vs_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1593_; 
v_vs_1567_ = lean_ctor_get(v_x_1533_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_x_1533_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1569_ = v_x_1533_;
v_isShared_1570_ = v_isSharedCheck_1593_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_vs_1567_);
lean_dec(v_x_1533_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1593_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
size_t v_sz_1571_; size_t v___x_1572_; lean_object* v___x_1573_; 
v_sz_1571_ = lean_array_size(v_vs_1567_);
v___x_1572_ = ((size_t)0ULL);
v___x_1573_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1571_, v___x_1572_, v_vs_1567_, v___y_1534_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1584_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1584_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1584_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v_a_1574_);
v___x_1579_ = v___x_1569_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1581_; 
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1579_);
v___x_1581_ = v___x_1576_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_del_object(v___x_1569_);
v_a_1585_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1573_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1573_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(size_t v_sz_1594_, size_t v_i_1595_, lean_object* v_bs_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v___x_1603_; 
v___x_1603_ = lean_usize_dec_lt(v_i_1595_, v_sz_1594_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v_bs_1596_);
return v___x_1604_;
}
else
{
lean_object* v_v_1605_; lean_object* v___x_1606_; lean_object* v_bs_x27_1607_; lean_object* v___x_1608_; 
v_v_1605_ = lean_array_uget(v_bs_1596_, v_i_1595_);
v___x_1606_ = lean_unsigned_to_nat(0u);
v_bs_x27_1607_ = lean_array_uset(v_bs_1596_, v_i_1595_, v___x_1606_);
v___x_1608_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_v_1605_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; size_t v___x_1610_; size_t v___x_1611_; lean_object* v___x_1612_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1608_, 1);
v___x_1610_ = ((size_t)1ULL);
v___x_1611_ = lean_usize_add(v_i_1595_, v___x_1610_);
v___x_1612_ = lean_array_uset(v_bs_x27_1607_, v_i_1595_, v_a_1609_);
v_i_1595_ = v___x_1611_;
v_bs_1596_ = v___x_1612_;
goto _start;
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec_ref(v_bs_x27_1607_);
v_a_1614_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1608_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1608_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_sz_1622_, lean_object* v_i_1623_, lean_object* v_bs_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
size_t v_sz_boxed_1631_; size_t v_i_boxed_1632_; lean_object* v_res_1633_; 
v_sz_boxed_1631_ = lean_unbox_usize(v_sz_1622_);
lean_dec(v_sz_1622_);
v_i_boxed_1632_ = lean_unbox_usize(v_i_1623_);
lean_dec(v_i_1623_);
v_res_1633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_boxed_1631_, v_i_boxed_1632_, v_bs_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(lean_object* v_x_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_x_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(lean_object* v_t_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_root_1649_; lean_object* v_tail_1650_; lean_object* v_size_1651_; size_t v_shift_1652_; lean_object* v_tailOff_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1689_; 
v_root_1649_ = lean_ctor_get(v_t_1642_, 0);
v_tail_1650_ = lean_ctor_get(v_t_1642_, 1);
v_size_1651_ = lean_ctor_get(v_t_1642_, 2);
v_shift_1652_ = lean_ctor_get_usize(v_t_1642_, 4);
v_tailOff_1653_ = lean_ctor_get(v_t_1642_, 3);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_t_1642_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1655_ = v_t_1642_;
v_isShared_1656_ = v_isSharedCheck_1689_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_tailOff_1653_);
lean_inc(v_size_1651_);
lean_inc(v_tail_1650_);
lean_inc(v_root_1649_);
lean_dec(v_t_1642_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1689_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_root_1649_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; size_t v_sz_1659_; size_t v___x_1660_; lean_object* v___x_1661_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v_sz_1659_ = lean_array_size(v_tail_1650_);
v___x_1660_ = ((size_t)0ULL);
v___x_1661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1659_, v___x_1660_, v_tail_1650_, v___y_1643_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1672_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1672_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1672_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v_a_1662_);
lean_ctor_set(v___x_1655_, 0, v_a_1658_);
v___x_1667_ = v___x_1655_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1658_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_a_1662_);
lean_ctor_set(v_reuseFailAlloc_1671_, 2, v_size_1651_);
lean_ctor_set(v_reuseFailAlloc_1671_, 3, v_tailOff_1653_);
lean_ctor_set_usize(v_reuseFailAlloc_1671_, 4, v_shift_1652_);
v___x_1667_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1669_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1667_);
v___x_1669_ = v___x_1664_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec(v_a_1658_);
lean_del_object(v___x_1655_);
lean_dec(v_tailOff_1653_);
lean_dec(v_size_1651_);
v_a_1673_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1661_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1661_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_del_object(v___x_1655_);
lean_dec(v_tailOff_1653_);
lean_dec(v_size_1651_);
lean_dec_ref(v_tail_1650_);
v_a_1681_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1657_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1657_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1___boxed(lean_object* v_t_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_t_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx(lean_object* v_ctx_1698_, lean_object* v_targetUses_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_decls_1705_; lean_object* v_fvarIdToDecl_1706_; lean_object* v_auxDeclToFullName_1707_; lean_object* v_size_1708_; lean_object* v_decls_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v_decls_1705_ = lean_ctor_get(v_ctx_1698_, 1);
lean_inc_ref(v_decls_1705_);
v_fvarIdToDecl_1706_ = lean_ctor_get(v_ctx_1698_, 0);
lean_inc_ref(v_fvarIdToDecl_1706_);
v_auxDeclToFullName_1707_ = lean_ctor_get(v_ctx_1698_, 2);
lean_inc(v_auxDeclToFullName_1707_);
v_size_1708_ = lean_ctor_get(v_decls_1705_, 2);
v_decls_1709_ = lean_mk_empty_array_with_capacity(v_size_1708_);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v_decls_1709_);
lean_ctor_set(v___x_1710_, 1, v_targetUses_1699_);
v___x_1711_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_ctx_1698_, v___x_1710_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v_fst_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1712_);
lean_dec_ref_known(v___x_1711_, 1);
v_fst_1713_ = lean_ctor_get(v_a_1712_, 0);
lean_inc(v_fst_1713_);
lean_dec(v_a_1712_);
v___x_1714_ = lean_st_mk_ref(v_fst_1713_);
v___x_1715_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_decls_1705_, v___x_1714_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1725_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1718_ = v___x_1715_;
v_isShared_1719_ = v_isSharedCheck_1725_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1725_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1720_ = lean_st_ref_get(v___x_1714_);
lean_dec(v___x_1714_);
lean_dec(v___x_1720_);
v___x_1721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1721_, 0, v_fvarIdToDecl_1706_);
lean_ctor_set(v___x_1721_, 1, v_a_1716_);
lean_ctor_set(v___x_1721_, 2, v_auxDeclToFullName_1707_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1721_);
v___x_1723_ = v___x_1718_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v___x_1714_);
lean_dec(v_auxDeclToFullName_1707_);
lean_dec_ref(v_fvarIdToDecl_1706_);
v_a_1726_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1715_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1715_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_dec(v_auxDeclToFullName_1707_);
lean_dec_ref(v_fvarIdToDecl_1706_);
lean_dec_ref(v_decls_1705_);
v_a_1734_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1711_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1711_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx___boxed(lean_object* v_ctx_1742_, lean_object* v_targetUses_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_ctx_1742_, v_targetUses_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(size_t v_sz_1750_, size_t v_i_1751_, lean_object* v_bs_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1750_, v_i_1751_, v_bs_1752_, v___y_1753_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(lean_object* v_sz_1760_, lean_object* v_i_1761_, lean_object* v_bs_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
size_t v_sz_boxed_1769_; size_t v_i_boxed_1770_; lean_object* v_res_1771_; 
v_sz_boxed_1769_ = lean_unbox_usize(v_sz_1760_);
lean_dec(v_sz_1760_);
v_i_boxed_1770_ = lean_unbox_usize(v_i_1761_);
lean_dec(v_i_1761_);
v_res_1771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(v_sz_boxed_1769_, v_i_boxed_1770_, v_bs_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
return v_res_1771_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_doNotDup(uint8_t v_u_1772_, lean_object* v_rhs_1773_, uint8_t v_elimTrivial_1774_){
_start:
{
uint8_t v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = 2;
v___x_1776_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_u_1772_, v___x_1775_);
if (v___x_1776_ == 0)
{
return v___x_1776_;
}
else
{
if (v_elimTrivial_1774_ == 0)
{
return v___x_1776_;
}
else
{
uint8_t v___x_1777_; 
v___x_1777_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_rhs_1773_);
if (v___x_1777_ == 0)
{
return v___x_1776_;
}
else
{
uint8_t v___x_1778_; 
v___x_1778_ = 0;
return v___x_1778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_doNotDup___boxed(lean_object* v_u_1779_, lean_object* v_rhs_1780_, lean_object* v_elimTrivial_1781_){
_start:
{
uint8_t v_u_boxed_1782_; uint8_t v_elimTrivial_boxed_1783_; uint8_t v_res_1784_; lean_object* v_r_1785_; 
v_u_boxed_1782_ = lean_unbox(v_u_1779_);
v_elimTrivial_boxed_1783_ = lean_unbox(v_elimTrivial_1781_);
v_res_1784_ = l_Lean_Elab_Tactic_Do_doNotDup(v_u_boxed_1782_, v_rhs_1780_, v_elimTrivial_boxed_1783_);
lean_dec_ref(v_rhs_1780_);
v_r_1785_ = lean_box(v_res_1784_);
return v_r_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(uint8_t v_elimTrivial_1788_, lean_object* v_e_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
if (lean_obj_tag(v_e_1789_) == 8)
{
lean_object* v_type_1796_; 
v_type_1796_ = lean_ctor_get(v_e_1789_, 1);
if (lean_obj_tag(v_type_1796_) == 10)
{
lean_object* v_value_1797_; lean_object* v_body_1798_; lean_object* v_data_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v_uses_1803_; uint8_t v___x_1804_; 
v_value_1797_ = lean_ctor_get(v_e_1789_, 2);
v_body_1798_ = lean_ctor_get(v_e_1789_, 3);
v_data_1799_ = lean_ctor_get(v_type_1796_, 0);
v___x_1800_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_1801_ = lean_unsigned_to_nat(2u);
v___x_1802_ = l_Lean_KVMap_getNat(v_data_1799_, v___x_1800_, v___x_1801_);
v_uses_1803_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_1802_);
lean_dec(v___x_1802_);
v___x_1804_ = l_Lean_Elab_Tactic_Do_doNotDup(v_uses_1803_, v_value_1797_, v_elimTrivial_1788_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = lean_expr_instantiate1(v_body_1798_, v_value_1797_);
v___x_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
return v___x_1807_;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
return v___x_1809_;
}
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
return v___x_1811_;
}
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(lean_object* v_elimTrivial_1814_, lean_object* v_e_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
uint8_t v_elimTrivial_boxed_1822_; lean_object* v_res_1823_; 
v_elimTrivial_boxed_1822_ = lean_unbox(v_elimTrivial_1814_);
v_res_1823_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(v_elimTrivial_boxed_1822_, v_e_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v_e_1815_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(lean_object* v_e_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v_e_1824_);
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(lean_object* v_e_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(v_e_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
return v_res_1840_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = l_Lean_maxRecDepthErrorMessage;
v___x_1847_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_1849_ = l_Lean_MessageData_ofFormat(v___x_1848_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_1851_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_1852_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
lean_ctor_set(v___x_1852_, 1, v___x_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_1853_){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v_ref_1853_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1858_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(lean_object* v_x_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___y_1870_; lean_object* v_toCold_1879_; lean_object* v_currRecDepth_1880_; lean_object* v_ref_1881_; uint16_t v_optionFlags_1882_; uint8_t v_suppressElabErrors_1883_; uint8_t v_isRecordingDeps_1884_; lean_object* v_maxRecDepth_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v_toCold_1879_ = lean_ctor_get(v___y_1866_, 0);
v_currRecDepth_1880_ = lean_ctor_get(v___y_1866_, 1);
v_ref_1881_ = lean_ctor_get(v___y_1866_, 2);
v_optionFlags_1882_ = lean_ctor_get_uint16(v___y_1866_, sizeof(void*)*3);
v_suppressElabErrors_1883_ = lean_ctor_get_uint8(v___y_1866_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1884_ = lean_ctor_get_uint8(v___y_1866_, sizeof(void*)*3 + 3);
v_maxRecDepth_1890_ = lean_ctor_get(v_toCold_1879_, 3);
v___x_1891_ = lean_unsigned_to_nat(0u);
v___x_1892_ = lean_nat_dec_eq(v_maxRecDepth_1890_, v___x_1891_);
if (v___x_1892_ == 0)
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_nat_dec_eq(v_currRecDepth_1880_, v_maxRecDepth_1890_);
if (v___x_1893_ == 0)
{
goto v___jp_1885_;
}
else
{
lean_object* v___x_1894_; 
lean_dec_ref(v_x_1861_);
lean_inc(v_ref_1881_);
v___x_1894_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1881_);
v___y_1870_ = v___x_1894_;
goto v___jp_1869_;
}
}
else
{
goto v___jp_1885_;
}
v___jp_1869_:
{
if (lean_obj_tag(v___y_1870_) == 0)
{
return v___y_1870_;
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
v_a_1871_ = lean_ctor_get(v___y_1870_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___y_1870_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___y_1870_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___y_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
v___jp_1885_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1886_ = lean_unsigned_to_nat(1u);
v___x_1887_ = lean_nat_add(v_currRecDepth_1880_, v___x_1886_);
lean_inc(v_ref_1881_);
lean_inc_ref(v_toCold_1879_);
v___x_1888_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1888_, 0, v_toCold_1879_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
lean_ctor_set(v___x_1888_, 2, v_ref_1881_);
lean_ctor_set_uint16(v___x_1888_, sizeof(void*)*3, v_optionFlags_1882_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 2, v_suppressElabErrors_1883_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 3, v_isRecordingDeps_1884_);
lean_inc(v___y_1867_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
lean_inc(v___y_1863_);
lean_inc(v___y_1862_);
v___x_1889_ = lean_apply_7(v_x_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___x_1888_, v___y_1867_, lean_box(0));
v___y_1870_ = v___x_1889_;
goto v___jp_1869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec(v___y_1896_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_1904_, lean_object* v_x_1905_){
_start:
{
if (lean_obj_tag(v_x_1905_) == 0)
{
lean_object* v___x_1906_; 
v___x_1906_ = lean_box(0);
return v___x_1906_;
}
else
{
lean_object* v_key_1907_; lean_object* v_value_1908_; lean_object* v_tail_1909_; uint8_t v___x_1910_; 
v_key_1907_ = lean_ctor_get(v_x_1905_, 0);
v_value_1908_ = lean_ctor_get(v_x_1905_, 1);
v_tail_1909_ = lean_ctor_get(v_x_1905_, 2);
v___x_1910_ = l_Lean_ExprStructEq_beq(v_key_1907_, v_a_1904_);
if (v___x_1910_ == 0)
{
v_x_1905_ = v_tail_1909_;
goto _start;
}
else
{
lean_object* v___x_1912_; 
lean_inc(v_value_1908_);
v___x_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1912_, 0, v_value_1908_);
return v___x_1912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_1913_, lean_object* v_x_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1913_, v_x_1914_);
lean_dec(v_x_1914_);
lean_dec_ref(v_a_1913_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object* v_m_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v_buckets_1918_; lean_object* v___x_1919_; uint64_t v___x_1920_; uint64_t v___x_1921_; uint64_t v___x_1922_; uint64_t v_fold_1923_; uint64_t v___x_1924_; uint64_t v___x_1925_; uint64_t v___x_1926_; size_t v___x_1927_; size_t v___x_1928_; size_t v___x_1929_; size_t v___x_1930_; size_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_buckets_1918_ = lean_ctor_get(v_m_1916_, 1);
v___x_1919_ = lean_array_get_size(v_buckets_1918_);
v___x_1920_ = l_Lean_ExprStructEq_hash(v_a_1917_);
v___x_1921_ = 32ULL;
v___x_1922_ = lean_uint64_shift_right(v___x_1920_, v___x_1921_);
v_fold_1923_ = lean_uint64_xor(v___x_1920_, v___x_1922_);
v___x_1924_ = 16ULL;
v___x_1925_ = lean_uint64_shift_right(v_fold_1923_, v___x_1924_);
v___x_1926_ = lean_uint64_xor(v_fold_1923_, v___x_1925_);
v___x_1927_ = lean_uint64_to_usize(v___x_1926_);
v___x_1928_ = lean_usize_of_nat(v___x_1919_);
v___x_1929_ = ((size_t)1ULL);
v___x_1930_ = lean_usize_sub(v___x_1928_, v___x_1929_);
v___x_1931_ = lean_usize_land(v___x_1927_, v___x_1930_);
v___x_1932_ = lean_array_uget_borrowed(v_buckets_1918_, v___x_1931_);
v___x_1933_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1917_, v___x_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_1934_, lean_object* v_a_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_1934_, v_a_1935_);
lean_dec_ref(v_a_1935_);
lean_dec_ref(v_m_1934_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v_b_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; 
lean_inc(v___y_1944_);
lean_inc_ref(v___y_1943_);
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1939_);
lean_inc(v___y_1938_);
v___x_1946_ = lean_apply_8(v_k_1937_, v_b_1940_, v___y_1938_, v___y_1939_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, lean_box(0));
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v_b_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_1947_, v___y_1948_, v___y_1949_, v_b_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1949_);
lean_dec(v___y_1948_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_1957_, lean_object* v_type_1958_, lean_object* v_val_1959_, lean_object* v_k_1960_, uint8_t v_nondep_1961_, uint8_t v_kind_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v___f_1970_; lean_object* v___x_1971_; 
lean_inc(v___y_1964_);
lean_inc(v___y_1963_);
v___f_1970_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1970_, 0, v_k_1960_);
lean_closure_set(v___f_1970_, 1, v___y_1963_);
lean_closure_set(v___f_1970_, 2, v___y_1964_);
v___x_1971_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1957_, v_type_1958_, v_val_1959_, v___f_1970_, v_nondep_1961_, v_kind_1962_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
if (lean_obj_tag(v___x_1971_) == 0)
{
return v___x_1971_;
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1971_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_1980_, lean_object* v_type_1981_, lean_object* v_val_1982_, lean_object* v_k_1983_, lean_object* v_nondep_1984_, lean_object* v_kind_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
uint8_t v_nondep_boxed_1993_; uint8_t v_kind_boxed_1994_; lean_object* v_res_1995_; 
v_nondep_boxed_1993_ = lean_unbox(v_nondep_1984_);
v_kind_boxed_1994_ = lean_unbox(v_kind_1985_);
v_res_1995_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1980_, v_type_1981_, v_val_1982_, v_k_1983_, v_nondep_boxed_1993_, v_kind_boxed_1994_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec(v___y_1986_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_1996_, uint8_t v_bi_1997_, lean_object* v_type_1998_, lean_object* v_k_1999_, uint8_t v_kind_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v___f_2008_; lean_object* v___x_2009_; 
lean_inc(v___y_2002_);
lean_inc(v___y_2001_);
v___f_2008_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2008_, 0, v_k_1999_);
lean_closure_set(v___f_2008_, 1, v___y_2001_);
lean_closure_set(v___f_2008_, 2, v___y_2002_);
v___x_2009_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1996_, v_bi_1997_, v_type_1998_, v___f_2008_, v_kind_2000_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
if (lean_obj_tag(v___x_2009_) == 0)
{
return v___x_2009_;
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_2018_, lean_object* v_bi_2019_, lean_object* v_type_2020_, lean_object* v_k_2021_, lean_object* v_kind_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
uint8_t v_bi_boxed_2030_; uint8_t v_kind_boxed_2031_; lean_object* v_res_2032_; 
v_bi_boxed_2030_ = lean_unbox(v_bi_2019_);
v_kind_boxed_2031_ = lean_unbox(v_kind_2022_);
v_res_2032_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_2018_, v_bi_boxed_2030_, v_type_2020_, v_k_2021_, v_kind_boxed_2031_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec(v___y_2023_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2033_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(v___x_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2049_, lean_object* v_x_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = lean_apply_1(v_x_2050_, lean_box(0));
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2059_, lean_object* v_x_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(v_00_u03b1_2059_, v_x_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_2068_, lean_object* v_x_2069_){
_start:
{
if (lean_obj_tag(v_x_2069_) == 0)
{
return v_x_2068_;
}
else
{
lean_object* v_key_2070_; lean_object* v_value_2071_; lean_object* v_tail_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2095_; 
v_key_2070_ = lean_ctor_get(v_x_2069_, 0);
v_value_2071_ = lean_ctor_get(v_x_2069_, 1);
v_tail_2072_ = lean_ctor_get(v_x_2069_, 2);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_x_2069_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2074_ = v_x_2069_;
v_isShared_2075_ = v_isSharedCheck_2095_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_tail_2072_);
lean_inc(v_value_2071_);
lean_inc(v_key_2070_);
lean_dec(v_x_2069_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2095_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; uint64_t v___x_2077_; uint64_t v___x_2078_; uint64_t v___x_2079_; uint64_t v_fold_2080_; uint64_t v___x_2081_; uint64_t v___x_2082_; uint64_t v___x_2083_; size_t v___x_2084_; size_t v___x_2085_; size_t v___x_2086_; size_t v___x_2087_; size_t v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2076_ = lean_array_get_size(v_x_2068_);
v___x_2077_ = l_Lean_ExprStructEq_hash(v_key_2070_);
v___x_2078_ = 32ULL;
v___x_2079_ = lean_uint64_shift_right(v___x_2077_, v___x_2078_);
v_fold_2080_ = lean_uint64_xor(v___x_2077_, v___x_2079_);
v___x_2081_ = 16ULL;
v___x_2082_ = lean_uint64_shift_right(v_fold_2080_, v___x_2081_);
v___x_2083_ = lean_uint64_xor(v_fold_2080_, v___x_2082_);
v___x_2084_ = lean_uint64_to_usize(v___x_2083_);
v___x_2085_ = lean_usize_of_nat(v___x_2076_);
v___x_2086_ = ((size_t)1ULL);
v___x_2087_ = lean_usize_sub(v___x_2085_, v___x_2086_);
v___x_2088_ = lean_usize_land(v___x_2084_, v___x_2087_);
v___x_2089_ = lean_array_uget_borrowed(v_x_2068_, v___x_2088_);
lean_inc(v___x_2089_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 2, v___x_2089_);
v___x_2091_ = v___x_2074_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_key_2070_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_value_2071_);
lean_ctor_set(v_reuseFailAlloc_2094_, 2, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; 
v___x_2092_ = lean_array_uset(v_x_2068_, v___x_2088_, v___x_2091_);
v_x_2068_ = v___x_2092_;
v_x_2069_ = v_tail_2072_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_2096_, lean_object* v_source_2097_, lean_object* v_target_2098_){
_start:
{
lean_object* v___x_2099_; uint8_t v___x_2100_; 
v___x_2099_ = lean_array_get_size(v_source_2097_);
v___x_2100_ = lean_nat_dec_lt(v_i_2096_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_dec_ref(v_source_2097_);
lean_dec(v_i_2096_);
return v_target_2098_;
}
else
{
lean_object* v_es_2101_; lean_object* v___x_2102_; lean_object* v_source_2103_; lean_object* v_target_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v_es_2101_ = lean_array_fget(v_source_2097_, v_i_2096_);
v___x_2102_ = lean_box(0);
v_source_2103_ = lean_array_fset(v_source_2097_, v_i_2096_, v___x_2102_);
v_target_2104_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_2098_, v_es_2101_);
v___x_2105_ = lean_unsigned_to_nat(1u);
v___x_2106_ = lean_nat_add(v_i_2096_, v___x_2105_);
lean_dec(v_i_2096_);
v_i_2096_ = v___x_2106_;
v_source_2097_ = v_source_2103_;
v_target_2098_ = v_target_2104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_2108_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v_nbuckets_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2109_ = lean_array_get_size(v_data_2108_);
v___x_2110_ = lean_unsigned_to_nat(2u);
v_nbuckets_2111_ = lean_nat_mul(v___x_2109_, v___x_2110_);
v___x_2112_ = lean_unsigned_to_nat(0u);
v___x_2113_ = lean_box(0);
v___x_2114_ = lean_mk_array(v_nbuckets_2111_, v___x_2113_);
v___x_2115_ = lean_array_propagate_mark(v_data_2108_, v___x_2114_);
v___x_2116_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_2112_, v_data_2108_, v___x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_2117_, lean_object* v_b_2118_, lean_object* v_x_2119_){
_start:
{
if (lean_obj_tag(v_x_2119_) == 0)
{
lean_dec(v_b_2118_);
lean_dec_ref(v_a_2117_);
return v_x_2119_;
}
else
{
lean_object* v_key_2120_; lean_object* v_value_2121_; lean_object* v_tail_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2134_; 
v_key_2120_ = lean_ctor_get(v_x_2119_, 0);
v_value_2121_ = lean_ctor_get(v_x_2119_, 1);
v_tail_2122_ = lean_ctor_get(v_x_2119_, 2);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_x_2119_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2124_ = v_x_2119_;
v_isShared_2125_ = v_isSharedCheck_2134_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_tail_2122_);
lean_inc(v_value_2121_);
lean_inc(v_key_2120_);
lean_dec(v_x_2119_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2134_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
uint8_t v___x_2126_; 
v___x_2126_ = l_Lean_ExprStructEq_beq(v_key_2120_, v_a_2117_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2117_, v_b_2118_, v_tail_2122_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 2, v___x_2127_);
v___x_2129_ = v___x_2124_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_key_2120_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_value_2121_);
lean_ctor_set(v_reuseFailAlloc_2130_, 2, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
else
{
lean_object* v___x_2132_; 
lean_dec(v_value_2121_);
lean_dec(v_key_2120_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 1, v_b_2118_);
lean_ctor_set(v___x_2124_, 0, v_a_2117_);
v___x_2132_ = v___x_2124_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2117_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_b_2118_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_tail_2122_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_2135_, lean_object* v_x_2136_){
_start:
{
if (lean_obj_tag(v_x_2136_) == 0)
{
uint8_t v___x_2137_; 
v___x_2137_ = 0;
return v___x_2137_;
}
else
{
lean_object* v_key_2138_; lean_object* v_tail_2139_; uint8_t v___x_2140_; 
v_key_2138_ = lean_ctor_get(v_x_2136_, 0);
v_tail_2139_ = lean_ctor_get(v_x_2136_, 2);
v___x_2140_ = l_Lean_ExprStructEq_beq(v_key_2138_, v_a_2135_);
if (v___x_2140_ == 0)
{
v_x_2136_ = v_tail_2139_;
goto _start;
}
else
{
return v___x_2140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_2142_, lean_object* v_x_2143_){
_start:
{
uint8_t v_res_2144_; lean_object* v_r_2145_; 
v_res_2144_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2142_, v_x_2143_);
lean_dec(v_x_2143_);
lean_dec_ref(v_a_2142_);
v_r_2145_ = lean_box(v_res_2144_);
return v_r_2145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object* v_m_2146_, lean_object* v_a_2147_, lean_object* v_b_2148_){
_start:
{
lean_object* v_size_2149_; lean_object* v_buckets_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2193_; 
v_size_2149_ = lean_ctor_get(v_m_2146_, 0);
v_buckets_2150_ = lean_ctor_get(v_m_2146_, 1);
v_isSharedCheck_2193_ = !lean_is_exclusive(v_m_2146_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2152_ = v_m_2146_;
v_isShared_2153_ = v_isSharedCheck_2193_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_buckets_2150_);
lean_inc(v_size_2149_);
lean_dec(v_m_2146_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2193_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; uint64_t v___x_2155_; uint64_t v___x_2156_; uint64_t v___x_2157_; uint64_t v_fold_2158_; uint64_t v___x_2159_; uint64_t v___x_2160_; uint64_t v___x_2161_; size_t v___x_2162_; size_t v___x_2163_; size_t v___x_2164_; size_t v___x_2165_; size_t v___x_2166_; lean_object* v_bkt_2167_; uint8_t v___x_2168_; 
v___x_2154_ = lean_array_get_size(v_buckets_2150_);
v___x_2155_ = l_Lean_ExprStructEq_hash(v_a_2147_);
v___x_2156_ = 32ULL;
v___x_2157_ = lean_uint64_shift_right(v___x_2155_, v___x_2156_);
v_fold_2158_ = lean_uint64_xor(v___x_2155_, v___x_2157_);
v___x_2159_ = 16ULL;
v___x_2160_ = lean_uint64_shift_right(v_fold_2158_, v___x_2159_);
v___x_2161_ = lean_uint64_xor(v_fold_2158_, v___x_2160_);
v___x_2162_ = lean_uint64_to_usize(v___x_2161_);
v___x_2163_ = lean_usize_of_nat(v___x_2154_);
v___x_2164_ = ((size_t)1ULL);
v___x_2165_ = lean_usize_sub(v___x_2163_, v___x_2164_);
v___x_2166_ = lean_usize_land(v___x_2162_, v___x_2165_);
v_bkt_2167_ = lean_array_uget_borrowed(v_buckets_2150_, v___x_2166_);
v___x_2168_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2147_, v_bkt_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; lean_object* v_size_x27_2170_; lean_object* v___x_2171_; lean_object* v_buckets_x27_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2169_ = lean_unsigned_to_nat(1u);
v_size_x27_2170_ = lean_nat_add(v_size_2149_, v___x_2169_);
lean_dec(v_size_2149_);
lean_inc(v_bkt_2167_);
v___x_2171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2171_, 0, v_a_2147_);
lean_ctor_set(v___x_2171_, 1, v_b_2148_);
lean_ctor_set(v___x_2171_, 2, v_bkt_2167_);
v_buckets_x27_2172_ = lean_array_uset(v_buckets_2150_, v___x_2166_, v___x_2171_);
v___x_2173_ = lean_unsigned_to_nat(4u);
v___x_2174_ = lean_nat_mul(v_size_x27_2170_, v___x_2173_);
v___x_2175_ = lean_unsigned_to_nat(3u);
v___x_2176_ = lean_nat_div(v___x_2174_, v___x_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_array_get_size(v_buckets_x27_2172_);
v___x_2178_ = lean_nat_dec_le(v___x_2176_, v___x_2177_);
lean_dec(v___x_2176_);
if (v___x_2178_ == 0)
{
lean_object* v_val_2179_; lean_object* v___x_2181_; 
v_val_2179_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_2172_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 1, v_val_2179_);
lean_ctor_set(v___x_2152_, 0, v_size_x27_2170_);
v___x_2181_ = v___x_2152_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_size_x27_2170_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_val_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
else
{
lean_object* v___x_2184_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 1, v_buckets_x27_2172_);
lean_ctor_set(v___x_2152_, 0, v_size_x27_2170_);
v___x_2184_ = v___x_2152_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_size_x27_2170_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_buckets_x27_2172_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
else
{
lean_object* v___x_2186_; lean_object* v_buckets_x27_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2191_; 
lean_inc(v_bkt_2167_);
v___x_2186_ = lean_box(0);
v_buckets_x27_2187_ = lean_array_uset(v_buckets_2150_, v___x_2166_, v___x_2186_);
v___x_2188_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2147_, v_b_2148_, v_bkt_2167_);
v___x_2189_ = lean_array_uset(v_buckets_x27_2187_, v___x_2166_, v___x_2188_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 1, v___x_2189_);
v___x_2191_ = v___x_2152_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_size_2149_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v___x_2189_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object* v_a_2194_, lean_object* v_e_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2198_ = lean_st_ref_take(v_a_2194_);
v___x_2199_ = lean_box(0);
v___x_2200_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v___x_2198_, v_e_2195_, v_a_2196_);
v___x_2201_ = lean_st_ref_put(v_a_2194_, v___x_2200_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2202_, lean_object* v_e_2203_, lean_object* v_a_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(v_a_2202_, v_e_2203_, v_a_2204_);
lean_dec(v_a_2202_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_2207_, lean_object* v_pre_2208_, lean_object* v_post_2209_, lean_object* v_usedLetOnly_2210_, lean_object* v_skipConstInApp_2211_, lean_object* v_skipInstances_2212_, lean_object* v_body_2213_, lean_object* v_x_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
uint8_t v_usedLetOnly_boxed_2222_; uint8_t v_skipConstInApp_boxed_2223_; uint8_t v_skipInstances_boxed_2224_; lean_object* v_res_2225_; 
v_usedLetOnly_boxed_2222_ = lean_unbox(v_usedLetOnly_2210_);
v_skipConstInApp_boxed_2223_ = lean_unbox(v_skipConstInApp_2211_);
v_skipInstances_boxed_2224_ = lean_unbox(v_skipInstances_2212_);
v_res_2225_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(v_fvars_2207_, v_pre_2208_, v_post_2209_, v_usedLetOnly_boxed_2222_, v_skipConstInApp_boxed_2223_, v_skipInstances_boxed_2224_, v_body_2213_, v_x_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec(v___y_2215_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_2229_, lean_object* v_pre_2230_, lean_object* v_post_2231_, uint8_t v_usedLetOnly_2232_, uint8_t v_skipConstInApp_2233_, uint8_t v_skipInstances_2234_, lean_object* v_body_2235_, lean_object* v_x_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = lean_array_push(v_fvars_2229_, v_x_2236_);
v___x_2245_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2230_, v_post_2231_, v_usedLetOnly_2232_, v_skipConstInApp_2233_, v_skipInstances_2234_, v___x_2244_, v_body_2235_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_2246_, lean_object* v_pre_2247_, lean_object* v_post_2248_, lean_object* v_usedLetOnly_2249_, lean_object* v_skipConstInApp_2250_, lean_object* v_skipInstances_2251_, lean_object* v_body_2252_, lean_object* v_x_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
uint8_t v_usedLetOnly_boxed_2261_; uint8_t v_skipConstInApp_boxed_2262_; uint8_t v_skipInstances_boxed_2263_; lean_object* v_res_2264_; 
v_usedLetOnly_boxed_2261_ = lean_unbox(v_usedLetOnly_2249_);
v_skipConstInApp_boxed_2262_ = lean_unbox(v_skipConstInApp_2250_);
v_skipInstances_boxed_2263_ = lean_unbox(v_skipInstances_2251_);
v_res_2264_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(v_fvars_2246_, v_pre_2247_, v_post_2248_, v_usedLetOnly_boxed_2261_, v_skipConstInApp_boxed_2262_, v_skipInstances_boxed_2263_, v_body_2252_, v_x_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec(v___y_2254_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(lean_object* v_pre_2265_, lean_object* v_post_2266_, uint8_t v_usedLetOnly_2267_, uint8_t v_skipConstInApp_2268_, uint8_t v_skipInstances_2269_, lean_object* v_e_2270_, lean_object* v_a_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v___x_2278_; 
lean_inc_ref(v_post_2266_);
lean_inc(v___y_2276_);
lean_inc_ref(v___y_2275_);
lean_inc(v___y_2274_);
lean_inc_ref(v___y_2273_);
lean_inc(v___y_2272_);
lean_inc_ref(v_e_2270_);
v___x_2278_ = lean_apply_7(v_post_2266_, v_e_2270_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, lean_box(0));
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2297_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2297_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2297_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
switch(lean_obj_tag(v_a_2279_))
{
case 0:
{
lean_object* v_e_2283_; lean_object* v___x_2285_; 
lean_dec_ref(v_e_2270_);
lean_dec_ref(v_post_2266_);
lean_dec_ref(v_pre_2265_);
v_e_2283_ = lean_ctor_get(v_a_2279_, 0);
lean_inc_ref(v_e_2283_);
lean_dec_ref_known(v_a_2279_, 1);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v_e_2283_);
v___x_2285_ = v___x_2281_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_e_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
case 1:
{
lean_object* v_e_2287_; lean_object* v___x_2288_; 
lean_del_object(v___x_2281_);
lean_dec_ref(v_e_2270_);
v_e_2287_ = lean_ctor_get(v_a_2279_, 0);
lean_inc_ref(v_e_2287_);
lean_dec_ref_known(v_a_2279_, 1);
v___x_2288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2265_, v_post_2266_, v_usedLetOnly_2267_, v_skipConstInApp_2268_, v_skipInstances_2269_, v_e_2287_, v_a_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
return v___x_2288_;
}
default: 
{
lean_object* v_e_x3f_2289_; 
lean_dec_ref(v_post_2266_);
lean_dec_ref(v_pre_2265_);
v_e_x3f_2289_ = lean_ctor_get(v_a_2279_, 0);
lean_inc(v_e_x3f_2289_);
lean_dec_ref_known(v_a_2279_, 1);
if (lean_obj_tag(v_e_x3f_2289_) == 0)
{
lean_object* v___x_2291_; 
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v_e_2270_);
v___x_2291_ = v___x_2281_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_e_2270_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
else
{
lean_object* v_val_2293_; lean_object* v___x_2295_; 
lean_dec_ref(v_e_2270_);
v_val_2293_ = lean_ctor_get(v_e_x3f_2289_, 0);
lean_inc(v_val_2293_);
lean_dec_ref_known(v_e_x3f_2289_, 1);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v_val_2293_);
v___x_2295_ = v___x_2281_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_val_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v_e_2270_);
lean_dec_ref(v_post_2266_);
lean_dec_ref(v_pre_2265_);
v_a_2298_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2278_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2278_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(lean_object* v_pre_2306_, lean_object* v_post_2307_, uint8_t v_usedLetOnly_2308_, uint8_t v_skipConstInApp_2309_, uint8_t v_skipInstances_2310_, lean_object* v_fvars_2311_, lean_object* v_e_2312_, lean_object* v_a_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
if (lean_obj_tag(v_e_2312_) == 6)
{
lean_object* v_binderName_2320_; lean_object* v_binderType_2321_; lean_object* v_body_2322_; uint8_t v_binderInfo_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___f_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v_binderName_2320_ = lean_ctor_get(v_e_2312_, 0);
lean_inc(v_binderName_2320_);
v_binderType_2321_ = lean_ctor_get(v_e_2312_, 1);
lean_inc_ref(v_binderType_2321_);
v_body_2322_ = lean_ctor_get(v_e_2312_, 2);
lean_inc_ref(v_body_2322_);
v_binderInfo_2323_ = lean_ctor_get_uint8(v_e_2312_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2312_, 3);
v___x_2324_ = lean_box(v_usedLetOnly_2308_);
v___x_2325_ = lean_box(v_skipConstInApp_2309_);
v___x_2326_ = lean_box(v_skipInstances_2310_);
lean_inc_ref(v_post_2307_);
lean_inc_ref(v_pre_2306_);
lean_inc_ref(v_fvars_2311_);
v___f_2327_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2327_, 0, v_fvars_2311_);
lean_closure_set(v___f_2327_, 1, v_pre_2306_);
lean_closure_set(v___f_2327_, 2, v_post_2307_);
lean_closure_set(v___f_2327_, 3, v___x_2324_);
lean_closure_set(v___f_2327_, 4, v___x_2325_);
lean_closure_set(v___f_2327_, 5, v___x_2326_);
lean_closure_set(v___f_2327_, 6, v_body_2322_);
v___x_2328_ = lean_expr_instantiate_rev(v_binderType_2321_, v_fvars_2311_);
lean_dec_ref(v_fvars_2311_);
lean_dec_ref(v_binderType_2321_);
v___x_2329_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2306_, v_post_2307_, v_usedLetOnly_2308_, v_skipConstInApp_2309_, v_skipInstances_2310_, v___x_2328_, v_a_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2329_, 1);
v___x_2331_ = 0;
v___x_2332_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2320_, v_binderInfo_2323_, v_a_2330_, v___f_2327_, v___x_2331_, v_a_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
return v___x_2332_;
}
else
{
lean_dec_ref(v___f_2327_);
lean_dec(v_binderName_2320_);
return v___x_2329_;
}
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = lean_expr_instantiate_rev(v_e_2312_, v_fvars_2311_);
lean_dec_ref(v_e_2312_);
lean_inc_ref(v_post_2307_);
lean_inc_ref(v_pre_2306_);
v___x_2334_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2306_, v_post_2307_, v_usedLetOnly_2308_, v_skipConstInApp_2309_, v_skipInstances_2310_, v___x_2333_, v_a_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; uint8_t v___x_2336_; uint8_t v___x_2337_; uint8_t v___x_2338_; lean_object* v___x_2339_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = 0;
v___x_2337_ = 1;
v___x_2338_ = 1;
v___x_2339_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2311_, v_a_2335_, v___x_2336_, v_usedLetOnly_2308_, v___x_2336_, v___x_2337_, v___x_2338_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec_ref(v_fvars_2311_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v___x_2341_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2306_, v_post_2307_, v_usedLetOnly_2308_, v_skipConstInApp_2309_, v_skipInstances_2310_, v_a_2340_, v_a_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
return v___x_2341_;
}
else
{
lean_dec_ref(v_post_2307_);
lean_dec_ref(v_pre_2306_);
return v___x_2339_;
}
}
else
{
lean_dec_ref(v_fvars_2311_);
lean_dec_ref(v_post_2307_);
lean_dec_ref(v_pre_2306_);
return v___x_2334_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_2342_, lean_object* v_pre_2343_, lean_object* v_post_2344_, uint8_t v_usedLetOnly_2345_, uint8_t v_skipConstInApp_2346_, uint8_t v_skipInstances_2347_, lean_object* v_body_2348_, lean_object* v_x_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = lean_array_push(v_fvars_2342_, v_x_2349_);
v___x_2358_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2343_, v_post_2344_, v_usedLetOnly_2345_, v_skipConstInApp_2346_, v_skipInstances_2347_, v___x_2357_, v_body_2348_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_2359_, lean_object* v_pre_2360_, lean_object* v_post_2361_, lean_object* v_usedLetOnly_2362_, lean_object* v_skipConstInApp_2363_, lean_object* v_skipInstances_2364_, lean_object* v_body_2365_, lean_object* v_x_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
uint8_t v_usedLetOnly_boxed_2374_; uint8_t v_skipConstInApp_boxed_2375_; uint8_t v_skipInstances_boxed_2376_; lean_object* v_res_2377_; 
v_usedLetOnly_boxed_2374_ = lean_unbox(v_usedLetOnly_2362_);
v_skipConstInApp_boxed_2375_ = lean_unbox(v_skipConstInApp_2363_);
v_skipInstances_boxed_2376_ = lean_unbox(v_skipInstances_2364_);
v_res_2377_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(v_fvars_2359_, v_pre_2360_, v_post_2361_, v_usedLetOnly_boxed_2374_, v_skipConstInApp_boxed_2375_, v_skipInstances_boxed_2376_, v_body_2365_, v_x_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec(v___y_2367_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(lean_object* v_pre_2378_, lean_object* v_post_2379_, uint8_t v_usedLetOnly_2380_, uint8_t v_skipConstInApp_2381_, uint8_t v_skipInstances_2382_, lean_object* v_fvars_2383_, lean_object* v_e_2384_, lean_object* v_a_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
if (lean_obj_tag(v_e_2384_) == 8)
{
lean_object* v_declName_2392_; lean_object* v_type_2393_; lean_object* v_value_2394_; lean_object* v_body_2395_; uint8_t v_nondep_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___f_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v_declName_2392_ = lean_ctor_get(v_e_2384_, 0);
lean_inc(v_declName_2392_);
v_type_2393_ = lean_ctor_get(v_e_2384_, 1);
lean_inc_ref(v_type_2393_);
v_value_2394_ = lean_ctor_get(v_e_2384_, 2);
lean_inc_ref(v_value_2394_);
v_body_2395_ = lean_ctor_get(v_e_2384_, 3);
lean_inc_ref(v_body_2395_);
v_nondep_2396_ = lean_ctor_get_uint8(v_e_2384_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2384_, 4);
v___x_2397_ = lean_box(v_usedLetOnly_2380_);
v___x_2398_ = lean_box(v_skipConstInApp_2381_);
v___x_2399_ = lean_box(v_skipInstances_2382_);
lean_inc_ref_n(v_post_2379_, 2);
lean_inc_ref_n(v_pre_2378_, 2);
lean_inc_ref(v_fvars_2383_);
v___f_2400_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2400_, 0, v_fvars_2383_);
lean_closure_set(v___f_2400_, 1, v_pre_2378_);
lean_closure_set(v___f_2400_, 2, v_post_2379_);
lean_closure_set(v___f_2400_, 3, v___x_2397_);
lean_closure_set(v___f_2400_, 4, v___x_2398_);
lean_closure_set(v___f_2400_, 5, v___x_2399_);
lean_closure_set(v___f_2400_, 6, v_body_2395_);
v___x_2401_ = lean_expr_instantiate_rev(v_type_2393_, v_fvars_2383_);
lean_dec_ref(v_type_2393_);
v___x_2402_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2378_, v_post_2379_, v_usedLetOnly_2380_, v_skipConstInApp_2381_, v_skipInstances_2382_, v___x_2401_, v_a_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref_known(v___x_2402_, 1);
v___x_2404_ = lean_expr_instantiate_rev(v_value_2394_, v_fvars_2383_);
lean_dec_ref(v_fvars_2383_);
lean_dec_ref(v_value_2394_);
v___x_2405_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2378_, v_post_2379_, v_usedLetOnly_2380_, v_skipConstInApp_2381_, v_skipInstances_2382_, v___x_2404_, v_a_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; uint8_t v___x_2407_; lean_object* v___x_2408_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref_known(v___x_2405_, 1);
v___x_2407_ = 0;
v___x_2408_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_2392_, v_a_2403_, v_a_2406_, v___f_2400_, v_nondep_2396_, v___x_2407_, v_a_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
return v___x_2408_;
}
else
{
lean_dec(v_a_2403_);
lean_dec_ref(v___f_2400_);
lean_dec(v_declName_2392_);
return v___x_2405_;
}
}
else
{
lean_dec_ref(v___f_2400_);
lean_dec_ref(v_value_2394_);
lean_dec(v_declName_2392_);
lean_dec_ref(v_fvars_2383_);
lean_dec_ref(v_post_2379_);
lean_dec_ref(v_pre_2378_);
return v___x_2402_;
}
}
else
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = lean_expr_instantiate_rev(v_e_2384_, v_fvars_2383_);
lean_dec_ref(v_e_2384_);
lean_inc_ref(v_post_2379_);
lean_inc_ref(v_pre_2378_);
v___x_2410_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2378_, v_post_2379_, v_usedLetOnly_2380_, v_skipConstInApp_2381_, v_skipInstances_2382_, v___x_2409_, v_a_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; uint8_t v___x_2412_; uint8_t v___x_2413_; lean_object* v___x_2414_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2411_);
lean_dec_ref_known(v___x_2410_, 1);
v___x_2412_ = 0;
v___x_2413_ = 1;
v___x_2414_ = l_Lean_Meta_mkLetFVars(v_fvars_2383_, v_a_2411_, v_usedLetOnly_2380_, v___x_2412_, v___x_2413_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec_ref(v_fvars_2383_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2416_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2414_, 1);
v___x_2416_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2378_, v_post_2379_, v_usedLetOnly_2380_, v_skipConstInApp_2381_, v_skipInstances_2382_, v_a_2415_, v_a_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
return v___x_2416_;
}
else
{
lean_dec_ref(v_post_2379_);
lean_dec_ref(v_pre_2378_);
return v___x_2414_;
}
}
else
{
lean_dec_ref(v_fvars_2383_);
lean_dec_ref(v_post_2379_);
lean_dec_ref(v_pre_2378_);
return v___x_2410_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2417_; lean_object* v_dummy_2418_; 
v___x_2417_ = lean_box(0);
v_dummy_2418_ = l_Lean_Expr_sort___override(v___x_2417_);
return v_dummy_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(lean_object* v_pre_2419_, lean_object* v_post_2420_, uint8_t v_usedLetOnly_2421_, uint8_t v_skipConstInApp_2422_, uint8_t v_skipInstances_2423_, size_t v_sz_2424_, size_t v_i_2425_, lean_object* v_bs_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
uint8_t v___x_2434_; 
v___x_2434_ = lean_usize_dec_lt(v_i_2425_, v_sz_2424_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; 
lean_dec_ref(v_post_2420_);
lean_dec_ref(v_pre_2419_);
v___x_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2435_, 0, v_bs_2426_);
return v___x_2435_;
}
else
{
lean_object* v_v_2436_; lean_object* v___x_2437_; lean_object* v_bs_x27_2438_; lean_object* v___x_2439_; 
v_v_2436_ = lean_array_uget(v_bs_2426_, v_i_2425_);
v___x_2437_ = lean_unsigned_to_nat(0u);
v_bs_x27_2438_ = lean_array_uset(v_bs_2426_, v_i_2425_, v___x_2437_);
lean_inc_ref(v_post_2420_);
lean_inc_ref(v_pre_2419_);
v___x_2439_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2419_, v_post_2420_, v_usedLetOnly_2421_, v_skipConstInApp_2422_, v_skipInstances_2423_, v_v_2436_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; size_t v___x_2441_; size_t v___x_2442_; lean_object* v___x_2443_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref_known(v___x_2439_, 1);
v___x_2441_ = ((size_t)1ULL);
v___x_2442_ = lean_usize_add(v_i_2425_, v___x_2441_);
v___x_2443_ = lean_array_uset(v_bs_x27_2438_, v_i_2425_, v_a_2440_);
v_i_2425_ = v___x_2442_;
v_bs_2426_ = v___x_2443_;
goto _start;
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec_ref(v_bs_x27_2438_);
lean_dec_ref(v_post_2420_);
lean_dec_ref(v_pre_2419_);
v_a_2445_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2439_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2439_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_2453_, lean_object* v_post_2454_, uint8_t v_usedLetOnly_2455_, uint8_t v_skipConstInApp_2456_, uint8_t v_skipInstances_2457_, lean_object* v___x_2458_, lean_object* v___y_2459_, lean_object* v_b_2460_, lean_object* v_a_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2453_, v_post_2454_, v_usedLetOnly_2455_, v_skipConstInApp_2456_, v_skipInstances_2457_, v___x_2458_, v___y_2459_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2478_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2471_ = v___x_2468_;
v_isShared_2472_ = v_isSharedCheck_2478_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2468_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2478_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
v___x_2473_ = lean_array_fset(v_b_2460_, v_a_2461_, v_a_2469_);
v___x_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v___x_2474_);
v___x_2476_ = v___x_2471_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec_ref(v_b_2460_);
v_a_2479_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2468_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2468_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_2487_, lean_object* v_post_2488_, lean_object* v_usedLetOnly_2489_, lean_object* v_skipConstInApp_2490_, lean_object* v_skipInstances_2491_, lean_object* v___x_2492_, lean_object* v___y_2493_, lean_object* v_b_2494_, lean_object* v_a_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
uint8_t v_usedLetOnly_boxed_2502_; uint8_t v_skipConstInApp_boxed_2503_; uint8_t v_skipInstances_boxed_2504_; lean_object* v_res_2505_; 
v_usedLetOnly_boxed_2502_ = lean_unbox(v_usedLetOnly_2489_);
v_skipConstInApp_boxed_2503_ = lean_unbox(v_skipConstInApp_2490_);
v_skipInstances_boxed_2504_ = lean_unbox(v_skipInstances_2491_);
v_res_2505_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_2487_, v_post_2488_, v_usedLetOnly_boxed_2502_, v_skipConstInApp_boxed_2503_, v_skipInstances_boxed_2504_, v___x_2492_, v___y_2493_, v_b_2494_, v_a_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec(v_a_2495_);
lean_dec(v___y_2493_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_2506_, lean_object* v___x_2507_, lean_object* v_pre_2508_, lean_object* v_post_2509_, uint8_t v_usedLetOnly_2510_, uint8_t v_skipConstInApp_2511_, uint8_t v_skipInstances_2512_, lean_object* v_a_2513_, lean_object* v_b_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___y_2523_; uint8_t v___x_2546_; 
v___x_2546_ = lean_nat_dec_lt(v_a_2513_, v_upperBound_2506_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; 
lean_dec(v_a_2513_);
lean_dec_ref(v_post_2509_);
lean_dec_ref(v_pre_2508_);
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v_b_2514_);
return v___x_2547_;
}
else
{
lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2548_ = lean_array_fget_borrowed(v_b_2514_, v_a_2513_);
v___x_2549_ = lean_array_get_size(v___x_2507_);
v___x_2550_ = lean_nat_dec_lt(v_a_2513_, v___x_2549_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___f_2554_; 
lean_inc(v___x_2548_);
v___x_2551_ = lean_box(v_usedLetOnly_2510_);
v___x_2552_ = lean_box(v_skipConstInApp_2511_);
v___x_2553_ = lean_box(v_skipInstances_2512_);
lean_inc(v_a_2513_);
lean_inc(v___y_2515_);
lean_inc_ref(v_post_2509_);
lean_inc_ref(v_pre_2508_);
v___f_2554_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2554_, 0, v_pre_2508_);
lean_closure_set(v___f_2554_, 1, v_post_2509_);
lean_closure_set(v___f_2554_, 2, v___x_2551_);
lean_closure_set(v___f_2554_, 3, v___x_2552_);
lean_closure_set(v___f_2554_, 4, v___x_2553_);
lean_closure_set(v___f_2554_, 5, v___x_2548_);
lean_closure_set(v___f_2554_, 6, v___y_2515_);
lean_closure_set(v___f_2554_, 7, v_b_2514_);
lean_closure_set(v___f_2554_, 8, v_a_2513_);
v___y_2523_ = v___f_2554_;
goto v___jp_2522_;
}
else
{
lean_object* v___x_2555_; uint8_t v_isInstance_2556_; 
v___x_2555_ = lean_array_fget_borrowed(v___x_2507_, v_a_2513_);
v_isInstance_2556_ = lean_ctor_get_uint8(v___x_2555_, sizeof(void*)*1 + 4);
if (v_isInstance_2556_ == 0)
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___f_2560_; 
lean_inc(v___x_2548_);
v___x_2557_ = lean_box(v_usedLetOnly_2510_);
v___x_2558_ = lean_box(v_skipConstInApp_2511_);
v___x_2559_ = lean_box(v_skipInstances_2512_);
lean_inc(v_a_2513_);
lean_inc(v___y_2515_);
lean_inc_ref(v_post_2509_);
lean_inc_ref(v_pre_2508_);
v___f_2560_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2560_, 0, v_pre_2508_);
lean_closure_set(v___f_2560_, 1, v_post_2509_);
lean_closure_set(v___f_2560_, 2, v___x_2557_);
lean_closure_set(v___f_2560_, 3, v___x_2558_);
lean_closure_set(v___f_2560_, 4, v___x_2559_);
lean_closure_set(v___f_2560_, 5, v___x_2548_);
lean_closure_set(v___f_2560_, 6, v___y_2515_);
lean_closure_set(v___f_2560_, 7, v_b_2514_);
lean_closure_set(v___f_2560_, 8, v_a_2513_);
v___y_2523_ = v___f_2560_;
goto v___jp_2522_;
}
else
{
lean_object* v___x_2561_; lean_object* v___f_2562_; 
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v_b_2514_);
v___f_2562_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2562_, 0, v___x_2561_);
v___y_2523_ = v___f_2562_;
goto v___jp_2522_;
}
}
}
v___jp_2522_:
{
lean_object* v___x_2524_; 
lean_inc(v___y_2520_);
lean_inc_ref(v___y_2519_);
lean_inc(v___y_2518_);
lean_inc_ref(v___y_2517_);
lean_inc(v___y_2516_);
v___x_2524_ = lean_apply_6(v___y_2523_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, lean_box(0));
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2537_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2537_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2537_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
if (lean_obj_tag(v_a_2525_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2531_; 
lean_dec(v_a_2513_);
lean_dec_ref(v_post_2509_);
lean_dec_ref(v_pre_2508_);
v_a_2529_ = lean_ctor_get(v_a_2525_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v_a_2525_, 1);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v_a_2529_);
v___x_2531_ = v___x_2527_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2529_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
lean_del_object(v___x_2527_);
v_a_2533_ = lean_ctor_get(v_a_2525_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v_a_2525_, 1);
v___x_2534_ = lean_unsigned_to_nat(1u);
v___x_2535_ = lean_nat_add(v_a_2513_, v___x_2534_);
lean_dec(v_a_2513_);
v_a_2513_ = v___x_2535_;
v_b_2514_ = v_a_2533_;
goto _start;
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v_a_2513_);
lean_dec_ref(v_post_2509_);
lean_dec_ref(v_pre_2508_);
v_a_2538_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2524_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2524_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(uint8_t v_skipInstances_2563_, lean_object* v_pre_2564_, lean_object* v_post_2565_, uint8_t v_usedLetOnly_2566_, uint8_t v_skipConstInApp_2567_, lean_object* v_x_2568_, lean_object* v_x_2569_, lean_object* v_x_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_f_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; 
if (lean_obj_tag(v_x_2568_) == 5)
{
lean_object* v_fn_2628_; lean_object* v_arg_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v_fn_2628_ = lean_ctor_get(v_x_2568_, 0);
lean_inc_ref(v_fn_2628_);
v_arg_2629_ = lean_ctor_get(v_x_2568_, 1);
lean_inc_ref(v_arg_2629_);
lean_dec_ref_known(v_x_2568_, 2);
v___x_2630_ = lean_array_set(v_x_2569_, v_x_2570_, v_arg_2629_);
v___x_2631_ = lean_unsigned_to_nat(1u);
v___x_2632_ = lean_nat_sub(v_x_2570_, v___x_2631_);
lean_dec(v_x_2570_);
v_x_2568_ = v_fn_2628_;
v_x_2569_ = v___x_2630_;
v_x_2570_ = v___x_2632_;
goto _start;
}
else
{
lean_dec(v_x_2570_);
if (v_skipConstInApp_2567_ == 0)
{
goto v___jp_2625_;
}
else
{
uint8_t v___x_2634_; 
v___x_2634_ = l_Lean_Expr_isConst(v_x_2568_);
if (v___x_2634_ == 0)
{
goto v___jp_2625_;
}
else
{
v_f_2579_ = v_x_2568_;
v___y_2580_ = v___y_2571_;
v___y_2581_ = v___y_2572_;
v___y_2582_ = v___y_2573_;
v___y_2583_ = v___y_2574_;
v___y_2584_ = v___y_2575_;
v___y_2585_ = v___y_2576_;
goto v___jp_2578_;
}
}
}
v___jp_2578_:
{
if (v_skipInstances_2563_ == 0)
{
size_t v_sz_2586_; size_t v___x_2587_; lean_object* v___x_2588_; 
v_sz_2586_ = lean_array_size(v_x_2569_);
v___x_2587_ = ((size_t)0ULL);
lean_inc_ref(v_post_2565_);
lean_inc_ref(v_pre_2564_);
v___x_2588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2564_, v_post_2565_, v_usedLetOnly_2566_, v_skipConstInApp_2567_, v_skipInstances_2563_, v_sz_2586_, v___x_2587_, v_x_2569_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
v___x_2590_ = l_Lean_mkAppN(v_f_2579_, v_a_2589_);
lean_dec(v_a_2589_);
v___x_2591_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2564_, v_post_2565_, v_usedLetOnly_2566_, v_skipConstInApp_2567_, v_skipInstances_2563_, v___x_2590_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
return v___x_2591_;
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec_ref(v_f_2579_);
lean_dec_ref(v_post_2565_);
lean_dec_ref(v_pre_2564_);
v_a_2592_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2588_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2588_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = lean_array_get_size(v_x_2569_);
lean_inc_ref(v_f_2579_);
v___x_2601_ = l_Lean_Meta_getFunInfoNArgs(v_f_2579_, v___x_2600_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v_paramInfo_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2602_);
lean_dec_ref_known(v___x_2601_, 1);
v_paramInfo_2603_ = lean_ctor_get(v_a_2602_, 0);
lean_inc_ref(v_paramInfo_2603_);
lean_dec(v_a_2602_);
v___x_2604_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2565_);
lean_inc_ref(v_pre_2564_);
v___x_2605_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v___x_2600_, v_paramInfo_2603_, v_pre_2564_, v_post_2565_, v_usedLetOnly_2566_, v_skipConstInApp_2567_, v_skipInstances_2563_, v___x_2604_, v_x_2569_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
lean_dec_ref(v_paramInfo_2603_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___x_2605_, 1);
v___x_2607_ = l_Lean_mkAppN(v_f_2579_, v_a_2606_);
lean_dec(v_a_2606_);
v___x_2608_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2564_, v_post_2565_, v_usedLetOnly_2566_, v_skipConstInApp_2567_, v_skipInstances_2563_, v___x_2607_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
return v___x_2608_;
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec_ref(v_f_2579_);
lean_dec_ref(v_post_2565_);
lean_dec_ref(v_pre_2564_);
v_a_2609_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2605_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2605_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec_ref(v_f_2579_);
lean_dec_ref(v_x_2569_);
lean_dec_ref(v_post_2565_);
lean_dec_ref(v_pre_2564_);
v_a_2617_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2601_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2601_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
v___jp_2625_:
{
lean_object* v___x_2626_; 
lean_inc_ref(v_post_2565_);
lean_inc_ref(v_pre_2564_);
v___x_2626_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2564_, v_post_2565_, v_usedLetOnly_2566_, v_skipConstInApp_2567_, v_skipInstances_2563_, v_x_2568_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2626_, 1);
v_f_2579_ = v_a_2627_;
v___y_2580_ = v___y_2571_;
v___y_2581_ = v___y_2572_;
v___y_2582_ = v___y_2573_;
v___y_2583_ = v___y_2574_;
v___y_2584_ = v___y_2575_;
v___y_2585_ = v___y_2576_;
goto v___jp_2578_;
}
else
{
lean_dec_ref(v_x_2569_);
lean_dec_ref(v_post_2565_);
lean_dec_ref(v_pre_2564_);
return v___x_2626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(lean_object* v___x_2635_, lean_object* v_pre_2636_, lean_object* v_e_2637_, lean_object* v_post_2638_, uint8_t v_usedLetOnly_2639_, uint8_t v_skipConstInApp_2640_, uint8_t v_skipInstances_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lean_Core_checkSystem(v___x_2635_, v___y_2646_, v___y_2647_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v___x_2650_; 
lean_dec_ref_known(v___x_2649_, 1);
lean_inc_ref(v_pre_2636_);
lean_inc(v___y_2647_);
lean_inc_ref(v___y_2646_);
lean_inc(v___y_2645_);
lean_inc_ref(v___y_2644_);
lean_inc(v___y_2643_);
lean_inc_ref(v_e_2637_);
v___x_2650_ = lean_apply_7(v_pre_2636_, v_e_2637_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, lean_box(0));
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2699_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2653_ = v___x_2650_;
v_isShared_2654_ = v_isSharedCheck_2699_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2650_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2699_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___y_2656_; 
switch(lean_obj_tag(v_a_2651_))
{
case 0:
{
lean_object* v_e_2691_; lean_object* v___x_2693_; 
lean_dec_ref(v_post_2638_);
lean_dec_ref(v_e_2637_);
lean_dec_ref(v_pre_2636_);
v_e_2691_ = lean_ctor_get(v_a_2651_, 0);
lean_inc_ref(v_e_2691_);
lean_dec_ref_known(v_a_2651_, 1);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 0, v_e_2691_);
v___x_2693_ = v___x_2653_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_e_2691_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
case 1:
{
lean_object* v_e_2695_; lean_object* v___x_2696_; 
lean_del_object(v___x_2653_);
lean_dec_ref(v_e_2637_);
v_e_2695_ = lean_ctor_get(v_a_2651_, 0);
lean_inc_ref(v_e_2695_);
lean_dec_ref_known(v_a_2651_, 1);
v___x_2696_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2636_, v_post_2638_, v_usedLetOnly_2639_, v_skipConstInApp_2640_, v_skipInstances_2641_, v_e_2695_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v___x_2696_;
}
default: 
{
lean_object* v_e_x3f_2697_; 
lean_del_object(v___x_2653_);
v_e_x3f_2697_ = lean_ctor_get(v_a_2651_, 0);
lean_inc(v_e_x3f_2697_);
lean_dec_ref_known(v_a_2651_, 1);
if (lean_obj_tag(v_e_x3f_2697_) == 0)
{
v___y_2656_ = v_e_2637_;
goto v___jp_2655_;
}
else
{
lean_object* v_val_2698_; 
lean_dec_ref(v_e_2637_);
v_val_2698_ = lean_ctor_get(v_e_x3f_2697_, 0);
lean_inc(v_val_2698_);
lean_dec_ref_known(v_e_x3f_2697_, 1);
v___y_2656_ = v_val_2698_;
goto v___jp_2655_;
}
}
}
v___jp_2655_:
{
switch(lean_obj_tag(v___y_2656_))
{
case 7:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2658_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2636_, v_post_2638_, v_usedLetOnly_2639_, v_skipConstInApp_2640_, v_skipInstances_2641_, v___x_2657_, v___y_2656_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v___x_2658_;
}
case 6:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2660_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2636_, v_post_2638_, v_usedLetOnly_2639_, v_skipConstInApp_2640_, v_skipInstances_2641_, v___x_2659_, v___y_2656_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v___x_2660_;
}
case 8:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2662_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2636_, v_post_2638_, v_usedLetOnly_2639_, v_skipConstInApp_2640_, v_skipInstances_2641_, v___x_2661_, v___y_2656_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v___x_2662_;
}
case 5:
{
lean_object* v_dummy_2663_; lean_object* v_nargs_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v_dummy_2663_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1);
v_nargs_2664_ = l_Lean_Expr_getAppNumArgs(v___y_2656_);
lean_inc(v_nargs_2664_);
v___x_2665_ = lean_mk_array(v_nargs_2664_, v_dummy_2663_);
v___x_2666_ = lean_unsigned_to_nat(1u);
v___x_2667_ = lean_nat_sub(v_nargs_2664_, v___x_2666_);
lean_dec(v_nargs_2664_);
v___x_2668_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_2641_, v_pre_2636_, v_post_2638_, v_usedLetOnly_2639_, v_skipConstInApp_2640_, v___y_2656_, v___x_2665_, v___x_2667_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v___x_2668_;
}
case 10:
{
lean_object* v_data_2669_; lean_object* v_expr_2670_; lean_object* v___x_2671_; 
v_data_2669_ = lean_ctor_get(v___y_2656_, 0);
v_expr_2670_ = lean_ctor_get(v___y_2656_, 1);
lean_inc_ref(v_expr_2670_);
lean_inc_ref(v_post_2638_);
lean_inc_ref(v_pre_2636_);
v___x_2671_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2636_, v_post_2638_, v_usedLetOnly_2639_, v_skipConstInApp_2640_, v_skipInstances_2641_, v_expr_2670_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; size_t v___x_2673_; size_t v___x_2674_; uint8_t v___x_2675_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2671_, 1);
v___x_2673_ = lean_ptr_addr(v_expr_2670_);
v___x_2674_ = lean_ptr_addr(v_a_2672_);
v___x_2675_ = lean_usize_dec_eq(v___x_2673_, v___x_2674_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
lean_inc(v_data_2669_);
lean_dec_ref_known(v___y_2656_, 2);
v___x_2676_ = l_Lean_Expr_mdata___override(v_data_2669_, v_a_2672_);
v___x_2677_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2636_, v_post_2638_, v_usedLetOnly_2639_, v_skipConstInApp_2640_, v_skipInstances_2641_, v___x_2676_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v___x_2677_;
}
else
{
lean_object* v___x_2678_; 
lean_dec(v_a_2672_);
v___x_2678_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2636_, v_post_2638_, v_usedLetOnly_2639_, v_skipConstInApp_2640_, v_skipInstances_2641_, v___y_2656_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v___x_2678_;
}
}
else
{
lean_dec_ref_known(v___y_2656_, 2);
lean_dec_ref(v_post_2638_);
lean_dec_ref(v_pre_2636_);
return v___x_2671_;
}
}
case 11:
{
lean_object* v_typeName_2679_; lean_object* v_idx_2680_; lean_object* v_struct_2681_; lean_object* v___x_2682_; 
v_typeName_2679_ = lean_ctor_get(v___y_2656_, 0);
v_idx_2680_ = lean_ctor_get(v___y_2656_, 1);
v_struct_2681_ = lean_ctor_get(v___y_2656_, 2);
lean_inc_ref(v_struct_2681_);
lean_inc_ref(v_post_2638_);
lean_inc_ref(v_pre_2636_);
v___x_2682_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2636_, v_post_2638_, v_usedLetOnly_2639_, v_skipConstInApp_2640_, v_skipInstances_2641_, v_struct_2681_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; size_t v___x_2684_; size_t v___x_2685_; uint8_t v___x_2686_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v___x_2684_ = lean_ptr_addr(v_struct_2681_);
v___x_2685_ = lean_ptr_addr(v_a_2683_);
v___x_2686_ = lean_usize_dec_eq(v___x_2684_, v___x_2685_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
lean_inc(v_idx_2680_);
lean_inc(v_typeName_2679_);
lean_dec_ref_known(v___y_2656_, 3);
v___x_2687_ = l_Lean_Expr_proj___override(v_typeName_2679_, v_idx_2680_, v_a_2683_);
v___x_2688_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2636_, v_post_2638_, v_usedLetOnly_2639_, v_skipConstInApp_2640_, v_skipInstances_2641_, v___x_2687_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v___x_2688_;
}
else
{
lean_object* v___x_2689_; 
lean_dec(v_a_2683_);
v___x_2689_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2636_, v_post_2638_, v_usedLetOnly_2639_, v_skipConstInApp_2640_, v_skipInstances_2641_, v___y_2656_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v___x_2689_;
}
}
else
{
lean_dec_ref_known(v___y_2656_, 3);
lean_dec_ref(v_post_2638_);
lean_dec_ref(v_pre_2636_);
return v___x_2682_;
}
}
default: 
{
lean_object* v___x_2690_; 
v___x_2690_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2636_, v_post_2638_, v_usedLetOnly_2639_, v_skipConstInApp_2640_, v_skipInstances_2641_, v___y_2656_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v___x_2690_;
}
}
}
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec_ref(v_post_2638_);
lean_dec_ref(v_e_2637_);
lean_dec_ref(v_pre_2636_);
v_a_2700_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2650_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2650_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_dec_ref(v_post_2638_);
lean_dec_ref(v_e_2637_);
lean_dec_ref(v_pre_2636_);
v_a_2708_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2649_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2649_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(lean_object* v___x_2716_, lean_object* v_pre_2717_, lean_object* v_e_2718_, lean_object* v_post_2719_, lean_object* v_usedLetOnly_2720_, lean_object* v_skipConstInApp_2721_, lean_object* v_skipInstances_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
uint8_t v_usedLetOnly_boxed_2730_; uint8_t v_skipConstInApp_boxed_2731_; uint8_t v_skipInstances_boxed_2732_; lean_object* v_res_2733_; 
v_usedLetOnly_boxed_2730_ = lean_unbox(v_usedLetOnly_2720_);
v_skipConstInApp_boxed_2731_ = lean_unbox(v_skipConstInApp_2721_);
v_skipInstances_boxed_2732_ = lean_unbox(v_skipInstances_2722_);
v_res_2733_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(v___x_2716_, v_pre_2717_, v_e_2718_, v_post_2719_, v_usedLetOnly_boxed_2730_, v_skipConstInApp_boxed_2731_, v_skipInstances_boxed_2732_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec(v___y_2723_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(lean_object* v_pre_2734_, lean_object* v_post_2735_, uint8_t v_usedLetOnly_2736_, uint8_t v_skipConstInApp_2737_, uint8_t v_skipInstances_2738_, lean_object* v_e_2739_, lean_object* v_a_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
lean_inc(v_a_2740_);
v___x_2747_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2747_, 0, lean_box(0));
lean_closure_set(v___x_2747_, 1, lean_box(0));
lean_closure_set(v___x_2747_, 2, v_a_2740_);
v___x_2748_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___x_2747_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2783_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2751_ = v___x_2748_;
v_isShared_2752_ = v_isSharedCheck_2783_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2748_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2783_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2753_; 
v___x_2753_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_a_2749_, v_e_2739_);
lean_dec(v_a_2749_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___f_2758_; lean_object* v___x_2759_; 
lean_del_object(v___x_2751_);
v___x_2754_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0));
v___x_2755_ = lean_box(v_usedLetOnly_2736_);
v___x_2756_ = lean_box(v_skipConstInApp_2737_);
v___x_2757_ = lean_box(v_skipInstances_2738_);
lean_inc_ref(v_e_2739_);
v___f_2758_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed), 14, 7);
lean_closure_set(v___f_2758_, 0, v___x_2754_);
lean_closure_set(v___f_2758_, 1, v_pre_2734_);
lean_closure_set(v___f_2758_, 2, v_e_2739_);
lean_closure_set(v___f_2758_, 3, v_post_2735_);
lean_closure_set(v___f_2758_, 4, v___x_2755_);
lean_closure_set(v___f_2758_, 5, v___x_2756_);
lean_closure_set(v___f_2758_, 6, v___x_2757_);
v___x_2759_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v___f_2758_, v_a_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___f_2761_; lean_object* v___x_2762_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc_n(v_a_2760_, 2);
lean_dec_ref_known(v___x_2759_, 1);
lean_inc(v_a_2740_);
v___f_2761_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2761_, 0, v_a_2740_);
lean_closure_set(v___f_2761_, 1, v_e_2739_);
lean_closure_set(v___f_2761_, 2, v_a_2760_);
v___x_2762_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___f_2761_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2769_ == 0)
{
lean_object* v_unused_2770_; 
v_unused_2770_ = lean_ctor_get(v___x_2762_, 0);
lean_dec(v_unused_2770_);
v___x_2764_ = v___x_2762_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_dec(v___x_2762_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v_a_2760_);
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2760_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v_a_2760_);
v_a_2771_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2762_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2762_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
else
{
lean_dec_ref(v_e_2739_);
return v___x_2759_;
}
}
else
{
lean_object* v_val_2779_; lean_object* v___x_2781_; 
lean_dec_ref(v_e_2739_);
lean_dec_ref(v_post_2735_);
lean_dec_ref(v_pre_2734_);
v_val_2779_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_val_2779_);
lean_dec_ref_known(v___x_2753_, 1);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 0, v_val_2779_);
v___x_2781_ = v___x_2751_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_val_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec_ref(v_e_2739_);
lean_dec_ref(v_post_2735_);
lean_dec_ref(v_pre_2734_);
v_a_2784_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2748_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2748_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object* v_pre_2792_, lean_object* v_post_2793_, uint8_t v_usedLetOnly_2794_, uint8_t v_skipConstInApp_2795_, uint8_t v_skipInstances_2796_, lean_object* v_fvars_2797_, lean_object* v_e_2798_, lean_object* v_a_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
if (lean_obj_tag(v_e_2798_) == 7)
{
lean_object* v_binderName_2806_; lean_object* v_binderType_2807_; lean_object* v_body_2808_; uint8_t v_binderInfo_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___f_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_binderName_2806_ = lean_ctor_get(v_e_2798_, 0);
lean_inc(v_binderName_2806_);
v_binderType_2807_ = lean_ctor_get(v_e_2798_, 1);
lean_inc_ref(v_binderType_2807_);
v_body_2808_ = lean_ctor_get(v_e_2798_, 2);
lean_inc_ref(v_body_2808_);
v_binderInfo_2809_ = lean_ctor_get_uint8(v_e_2798_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2798_, 3);
v___x_2810_ = lean_box(v_usedLetOnly_2794_);
v___x_2811_ = lean_box(v_skipConstInApp_2795_);
v___x_2812_ = lean_box(v_skipInstances_2796_);
lean_inc_ref(v_post_2793_);
lean_inc_ref(v_pre_2792_);
lean_inc_ref(v_fvars_2797_);
v___f_2813_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2813_, 0, v_fvars_2797_);
lean_closure_set(v___f_2813_, 1, v_pre_2792_);
lean_closure_set(v___f_2813_, 2, v_post_2793_);
lean_closure_set(v___f_2813_, 3, v___x_2810_);
lean_closure_set(v___f_2813_, 4, v___x_2811_);
lean_closure_set(v___f_2813_, 5, v___x_2812_);
lean_closure_set(v___f_2813_, 6, v_body_2808_);
v___x_2814_ = lean_expr_instantiate_rev(v_binderType_2807_, v_fvars_2797_);
lean_dec_ref(v_fvars_2797_);
lean_dec_ref(v_binderType_2807_);
v___x_2815_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2792_, v_post_2793_, v_usedLetOnly_2794_, v_skipConstInApp_2795_, v_skipInstances_2796_, v___x_2814_, v_a_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; uint8_t v___x_2817_; lean_object* v___x_2818_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2815_, 1);
v___x_2817_ = 0;
v___x_2818_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2806_, v_binderInfo_2809_, v_a_2816_, v___f_2813_, v___x_2817_, v_a_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
return v___x_2818_;
}
else
{
lean_dec_ref(v___f_2813_);
lean_dec(v_binderName_2806_);
return v___x_2815_;
}
}
else
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = lean_expr_instantiate_rev(v_e_2798_, v_fvars_2797_);
lean_dec_ref(v_e_2798_);
lean_inc_ref(v_post_2793_);
lean_inc_ref(v_pre_2792_);
v___x_2820_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2792_, v_post_2793_, v_usedLetOnly_2794_, v_skipConstInApp_2795_, v_skipInstances_2796_, v___x_2819_, v_a_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; uint8_t v___x_2822_; uint8_t v___x_2823_; uint8_t v___x_2824_; lean_object* v___x_2825_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = 0;
v___x_2823_ = 1;
v___x_2824_ = 1;
v___x_2825_ = l_Lean_Meta_mkForallFVars(v_fvars_2797_, v_a_2821_, v___x_2822_, v_usedLetOnly_2794_, v___x_2823_, v___x_2824_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec_ref(v_fvars_2797_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2827_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
v___x_2827_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2792_, v_post_2793_, v_usedLetOnly_2794_, v_skipConstInApp_2795_, v_skipInstances_2796_, v_a_2826_, v_a_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
return v___x_2827_;
}
else
{
lean_dec_ref(v_post_2793_);
lean_dec_ref(v_pre_2792_);
return v___x_2825_;
}
}
else
{
lean_dec_ref(v_fvars_2797_);
lean_dec_ref(v_post_2793_);
lean_dec_ref(v_pre_2792_);
return v___x_2820_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_2828_, lean_object* v_pre_2829_, lean_object* v_post_2830_, uint8_t v_usedLetOnly_2831_, uint8_t v_skipConstInApp_2832_, uint8_t v_skipInstances_2833_, lean_object* v_body_2834_, lean_object* v_x_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = lean_array_push(v_fvars_2828_, v_x_2835_);
v___x_2844_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2829_, v_post_2830_, v_usedLetOnly_2831_, v_skipConstInApp_2832_, v_skipInstances_2833_, v___x_2843_, v_body_2834_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2845_, lean_object* v_post_2846_, lean_object* v_usedLetOnly_2847_, lean_object* v_skipConstInApp_2848_, lean_object* v_skipInstances_2849_, lean_object* v_e_2850_, lean_object* v_a_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
uint8_t v_usedLetOnly_boxed_2858_; uint8_t v_skipConstInApp_boxed_2859_; uint8_t v_skipInstances_boxed_2860_; lean_object* v_res_2861_; 
v_usedLetOnly_boxed_2858_ = lean_unbox(v_usedLetOnly_2847_);
v_skipConstInApp_boxed_2859_ = lean_unbox(v_skipConstInApp_2848_);
v_skipInstances_boxed_2860_ = lean_unbox(v_skipInstances_2849_);
v_res_2861_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2845_, v_post_2846_, v_usedLetOnly_boxed_2858_, v_skipConstInApp_boxed_2859_, v_skipInstances_boxed_2860_, v_e_2850_, v_a_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec(v_a_2851_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_2862_, lean_object* v_post_2863_, lean_object* v_usedLetOnly_2864_, lean_object* v_skipConstInApp_2865_, lean_object* v_skipInstances_2866_, lean_object* v_sz_2867_, lean_object* v_i_2868_, lean_object* v_bs_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
uint8_t v_usedLetOnly_boxed_2877_; uint8_t v_skipConstInApp_boxed_2878_; uint8_t v_skipInstances_boxed_2879_; size_t v_sz_boxed_2880_; size_t v_i_boxed_2881_; lean_object* v_res_2882_; 
v_usedLetOnly_boxed_2877_ = lean_unbox(v_usedLetOnly_2864_);
v_skipConstInApp_boxed_2878_ = lean_unbox(v_skipConstInApp_2865_);
v_skipInstances_boxed_2879_ = lean_unbox(v_skipInstances_2866_);
v_sz_boxed_2880_ = lean_unbox_usize(v_sz_2867_);
lean_dec(v_sz_2867_);
v_i_boxed_2881_ = lean_unbox_usize(v_i_2868_);
lean_dec(v_i_2868_);
v_res_2882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2862_, v_post_2863_, v_usedLetOnly_boxed_2877_, v_skipConstInApp_boxed_2878_, v_skipInstances_boxed_2879_, v_sz_boxed_2880_, v_i_boxed_2881_, v_bs_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec(v___y_2870_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object* v_pre_2883_, lean_object* v_post_2884_, lean_object* v_usedLetOnly_2885_, lean_object* v_skipConstInApp_2886_, lean_object* v_skipInstances_2887_, lean_object* v_e_2888_, lean_object* v_a_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
uint8_t v_usedLetOnly_boxed_2896_; uint8_t v_skipConstInApp_boxed_2897_; uint8_t v_skipInstances_boxed_2898_; lean_object* v_res_2899_; 
v_usedLetOnly_boxed_2896_ = lean_unbox(v_usedLetOnly_2885_);
v_skipConstInApp_boxed_2897_ = lean_unbox(v_skipConstInApp_2886_);
v_skipInstances_boxed_2898_ = lean_unbox(v_skipInstances_2887_);
v_res_2899_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2883_, v_post_2884_, v_usedLetOnly_boxed_2896_, v_skipConstInApp_boxed_2897_, v_skipInstances_boxed_2898_, v_e_2888_, v_a_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v_a_2889_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_2900_, lean_object* v_post_2901_, lean_object* v_usedLetOnly_2902_, lean_object* v_skipConstInApp_2903_, lean_object* v_skipInstances_2904_, lean_object* v_fvars_2905_, lean_object* v_e_2906_, lean_object* v_a_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
uint8_t v_usedLetOnly_boxed_2914_; uint8_t v_skipConstInApp_boxed_2915_; uint8_t v_skipInstances_boxed_2916_; lean_object* v_res_2917_; 
v_usedLetOnly_boxed_2914_ = lean_unbox(v_usedLetOnly_2902_);
v_skipConstInApp_boxed_2915_ = lean_unbox(v_skipConstInApp_2903_);
v_skipInstances_boxed_2916_ = lean_unbox(v_skipInstances_2904_);
v_res_2917_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2900_, v_post_2901_, v_usedLetOnly_boxed_2914_, v_skipConstInApp_boxed_2915_, v_skipInstances_boxed_2916_, v_fvars_2905_, v_e_2906_, v_a_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec(v_a_2907_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_2918_, lean_object* v_post_2919_, lean_object* v_usedLetOnly_2920_, lean_object* v_skipConstInApp_2921_, lean_object* v_skipInstances_2922_, lean_object* v_fvars_2923_, lean_object* v_e_2924_, lean_object* v_a_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
uint8_t v_usedLetOnly_boxed_2932_; uint8_t v_skipConstInApp_boxed_2933_; uint8_t v_skipInstances_boxed_2934_; lean_object* v_res_2935_; 
v_usedLetOnly_boxed_2932_ = lean_unbox(v_usedLetOnly_2920_);
v_skipConstInApp_boxed_2933_ = lean_unbox(v_skipConstInApp_2921_);
v_skipInstances_boxed_2934_ = lean_unbox(v_skipInstances_2922_);
v_res_2935_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2918_, v_post_2919_, v_usedLetOnly_boxed_2932_, v_skipConstInApp_boxed_2933_, v_skipInstances_boxed_2934_, v_fvars_2923_, v_e_2924_, v_a_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec(v_a_2925_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_2936_, lean_object* v_post_2937_, lean_object* v_usedLetOnly_2938_, lean_object* v_skipConstInApp_2939_, lean_object* v_skipInstances_2940_, lean_object* v_fvars_2941_, lean_object* v_e_2942_, lean_object* v_a_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
uint8_t v_usedLetOnly_boxed_2950_; uint8_t v_skipConstInApp_boxed_2951_; uint8_t v_skipInstances_boxed_2952_; lean_object* v_res_2953_; 
v_usedLetOnly_boxed_2950_ = lean_unbox(v_usedLetOnly_2938_);
v_skipConstInApp_boxed_2951_ = lean_unbox(v_skipConstInApp_2939_);
v_skipInstances_boxed_2952_ = lean_unbox(v_skipInstances_2940_);
v_res_2953_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2936_, v_post_2937_, v_usedLetOnly_boxed_2950_, v_skipConstInApp_boxed_2951_, v_skipInstances_boxed_2952_, v_fvars_2941_, v_e_2942_, v_a_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec(v___y_2944_);
lean_dec(v_a_2943_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_2954_, lean_object* v___x_2955_, lean_object* v_pre_2956_, lean_object* v_post_2957_, lean_object* v_usedLetOnly_2958_, lean_object* v_skipConstInApp_2959_, lean_object* v_skipInstances_2960_, lean_object* v_a_2961_, lean_object* v_b_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
uint8_t v_usedLetOnly_boxed_2970_; uint8_t v_skipConstInApp_boxed_2971_; uint8_t v_skipInstances_boxed_2972_; lean_object* v_res_2973_; 
v_usedLetOnly_boxed_2970_ = lean_unbox(v_usedLetOnly_2958_);
v_skipConstInApp_boxed_2971_ = lean_unbox(v_skipConstInApp_2959_);
v_skipInstances_boxed_2972_ = lean_unbox(v_skipInstances_2960_);
v_res_2973_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_2954_, v___x_2955_, v_pre_2956_, v_post_2957_, v_usedLetOnly_boxed_2970_, v_skipConstInApp_boxed_2971_, v_skipInstances_boxed_2972_, v_a_2961_, v_b_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___x_2955_);
lean_dec(v_upperBound_2954_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_2974_, lean_object* v_pre_2975_, lean_object* v_post_2976_, lean_object* v_usedLetOnly_2977_, lean_object* v_skipConstInApp_2978_, lean_object* v_x_2979_, lean_object* v_x_2980_, lean_object* v_x_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
uint8_t v_skipInstances_boxed_2989_; uint8_t v_usedLetOnly_boxed_2990_; uint8_t v_skipConstInApp_boxed_2991_; lean_object* v_res_2992_; 
v_skipInstances_boxed_2989_ = lean_unbox(v_skipInstances_2974_);
v_usedLetOnly_boxed_2990_ = lean_unbox(v_usedLetOnly_2977_);
v_skipConstInApp_boxed_2991_ = lean_unbox(v_skipConstInApp_2978_);
v_res_2992_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_boxed_2989_, v_pre_2975_, v_post_2976_, v_usedLetOnly_boxed_2990_, v_skipConstInApp_boxed_2991_, v_x_2979_, v_x_2980_, v_x_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v___y_2982_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object* v_00_u03b1_2993_, lean_object* v_x_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = lean_apply_1(v_x_2994_, lean_box(0));
v___x_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3003_, lean_object* v_x_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(v_00_u03b1_3003_, v_x_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
return v_res_3011_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = lean_box(0);
v___x_3013_ = lean_unsigned_to_nat(16u);
v___x_3014_ = lean_mk_array(v___x_3013_, v___x_3012_);
return v___x_3014_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0);
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
lean_ctor_set(v___x_3017_, 1, v___x_3015_);
return v___x_3017_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1);
v___x_3019_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3019_, 0, lean_box(0));
lean_closure_set(v___x_3019_, 1, lean_box(0));
lean_closure_set(v___x_3019_, 2, v___x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object* v_input_3020_, lean_object* v_pre_3021_, lean_object* v_post_3022_, uint8_t v_usedLetOnly_3023_, uint8_t v_skipConstInApp_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
uint8_t v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v_a_3034_; lean_object* v___x_3035_; 
v___x_3031_ = 0;
v___x_3032_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2);
v___x_3033_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3032_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref(v___x_3033_);
v___x_3035_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_3021_, v_post_3022_, v_usedLetOnly_3023_, v_skipConstInApp_3024_, v___x_3031_, v_input_3020_, v_a_3034_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
lean_dec_ref_known(v___x_3035_, 1);
v___x_3037_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3037_, 0, lean_box(0));
lean_closure_set(v___x_3037_, 1, lean_box(0));
lean_closure_set(v___x_3037_, 2, v_a_3034_);
v___x_3038_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3037_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3045_ == 0)
{
lean_object* v_unused_3046_; 
v_unused_3046_ = lean_ctor_get(v___x_3038_, 0);
lean_dec(v_unused_3046_);
v___x_3040_ = v___x_3038_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_dec(v___x_3038_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v_a_3036_);
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3036_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
else
{
lean_dec(v_a_3034_);
return v___x_3035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object* v_input_3047_, lean_object* v_pre_3048_, lean_object* v_post_3049_, lean_object* v_usedLetOnly_3050_, lean_object* v_skipConstInApp_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_){
_start:
{
uint8_t v_usedLetOnly_boxed_3058_; uint8_t v_skipConstInApp_boxed_3059_; lean_object* v_res_3060_; 
v_usedLetOnly_boxed_3058_ = lean_unbox(v_usedLetOnly_3050_);
v_skipConstInApp_boxed_3059_ = lean_unbox(v_skipConstInApp_3051_);
v_res_3060_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_input_3047_, v_pre_3048_, v_post_3049_, v_usedLetOnly_boxed_3058_, v_skipConstInApp_boxed_3059_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object* v_e_3062_, uint8_t v_elimTrivial_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_){
_start:
{
lean_object* v___x_3069_; lean_object* v_pre_3070_; lean_object* v___f_3071_; uint8_t v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3069_ = lean_box(v_elimTrivial_3063_);
v_pre_3070_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed), 8, 1);
lean_closure_set(v_pre_3070_, 0, v___x_3069_);
v___f_3071_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0));
v___x_3072_ = 0;
v___x_3073_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_3074_ = lean_st_mk_ref(v___x_3073_);
v___x_3075_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_e_3062_, v_pre_3070_, v___f_3071_, v___x_3072_, v___x_3072_, v___x_3074_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3084_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3084_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3084_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3080_ = lean_st_ref_get(v___x_3074_);
lean_dec(v___x_3074_);
lean_dec(v___x_3080_);
if (v_isShared_3079_ == 0)
{
v___x_3082_ = v___x_3078_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3076_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
else
{
lean_dec(v___x_3074_);
return v___x_3075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object* v_e_3085_, lean_object* v_elimTrivial_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
uint8_t v_elimTrivial_boxed_3092_; lean_object* v_res_3093_; 
v_elimTrivial_boxed_3092_ = lean_unbox(v_elimTrivial_3086_);
v_res_3093_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v_e_3085_, v_elimTrivial_boxed_3092_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object* v_upperBound_3094_, lean_object* v___x_3095_, lean_object* v_pre_3096_, lean_object* v_post_3097_, uint8_t v_usedLetOnly_3098_, uint8_t v_skipConstInApp_3099_, uint8_t v_skipInstances_3100_, lean_object* v___x_3101_, lean_object* v_inst_3102_, lean_object* v_R_3103_, lean_object* v_a_3104_, lean_object* v_b_3105_, lean_object* v_c_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v___x_3114_; 
v___x_3114_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_3094_, v___x_3095_, v_pre_3096_, v_post_3097_, v_usedLetOnly_3098_, v_skipConstInApp_3099_, v_skipInstances_3100_, v_a_3104_, v_b_3105_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_3115_ = _args[0];
lean_object* v___x_3116_ = _args[1];
lean_object* v_pre_3117_ = _args[2];
lean_object* v_post_3118_ = _args[3];
lean_object* v_usedLetOnly_3119_ = _args[4];
lean_object* v_skipConstInApp_3120_ = _args[5];
lean_object* v_skipInstances_3121_ = _args[6];
lean_object* v___x_3122_ = _args[7];
lean_object* v_inst_3123_ = _args[8];
lean_object* v_R_3124_ = _args[9];
lean_object* v_a_3125_ = _args[10];
lean_object* v_b_3126_ = _args[11];
lean_object* v_c_3127_ = _args[12];
lean_object* v___y_3128_ = _args[13];
lean_object* v___y_3129_ = _args[14];
lean_object* v___y_3130_ = _args[15];
lean_object* v___y_3131_ = _args[16];
lean_object* v___y_3132_ = _args[17];
lean_object* v___y_3133_ = _args[18];
lean_object* v___y_3134_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_3135_; uint8_t v_skipConstInApp_boxed_3136_; uint8_t v_skipInstances_boxed_3137_; lean_object* v_res_3138_; 
v_usedLetOnly_boxed_3135_ = lean_unbox(v_usedLetOnly_3119_);
v_skipConstInApp_boxed_3136_ = lean_unbox(v_skipConstInApp_3120_);
v_skipInstances_boxed_3137_ = lean_unbox(v_skipInstances_3121_);
v_res_3138_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_upperBound_3115_, v___x_3116_, v_pre_3117_, v_post_3118_, v_usedLetOnly_boxed_3135_, v_skipConstInApp_boxed_3136_, v_skipInstances_boxed_3137_, v___x_3122_, v_inst_3123_, v_R_3124_, v_a_3125_, v_b_3126_, v_c_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec(v___x_3122_);
lean_dec_ref(v___x_3116_);
lean_dec(v_upperBound_3115_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3139_, lean_object* v_m_3140_, lean_object* v_a_3141_){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_3140_, v_a_3141_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_3143_, lean_object* v_m_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(v_00_u03b2_3143_, v_m_3144_, v_a_3145_);
lean_dec_ref(v_a_3145_);
lean_dec_ref(v_m_3144_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_3147_, lean_object* v_name_3148_, uint8_t v_bi_3149_, lean_object* v_type_3150_, lean_object* v_k_3151_, uint8_t v_kind_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v___x_3160_; 
v___x_3160_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_3148_, v_bi_3149_, v_type_3150_, v_k_3151_, v_kind_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3161_, lean_object* v_name_3162_, lean_object* v_bi_3163_, lean_object* v_type_3164_, lean_object* v_k_3165_, lean_object* v_kind_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
uint8_t v_bi_boxed_3174_; uint8_t v_kind_boxed_3175_; lean_object* v_res_3176_; 
v_bi_boxed_3174_ = lean_unbox(v_bi_3163_);
v_kind_boxed_3175_ = lean_unbox(v_kind_3166_);
v_res_3176_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_3161_, v_name_3162_, v_bi_boxed_3174_, v_type_3164_, v_k_3165_, v_kind_boxed_3175_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec(v___y_3167_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_3177_, lean_object* v_name_3178_, lean_object* v_type_3179_, lean_object* v_val_3180_, lean_object* v_k_3181_, uint8_t v_nondep_3182_, uint8_t v_kind_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_3178_, v_type_3179_, v_val_3180_, v_k_3181_, v_nondep_3182_, v_kind_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_3192_, lean_object* v_name_3193_, lean_object* v_type_3194_, lean_object* v_val_3195_, lean_object* v_k_3196_, lean_object* v_nondep_3197_, lean_object* v_kind_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
uint8_t v_nondep_boxed_3206_; uint8_t v_kind_boxed_3207_; lean_object* v_res_3208_; 
v_nondep_boxed_3206_ = lean_unbox(v_nondep_3197_);
v_kind_boxed_3207_ = lean_unbox(v_kind_3198_);
v_res_3208_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_3192_, v_name_3193_, v_type_3194_, v_val_3195_, v_k_3196_, v_nondep_boxed_3206_, v_kind_boxed_3207_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___y_3200_);
lean_dec(v___y_3199_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_3209_, lean_object* v_ref_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_3210_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_3217_, lean_object* v_ref_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_3217_, v_ref_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_3225_, lean_object* v_x_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_3235_, lean_object* v_x_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(v_00_u03b1_3235_, v_x_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec(v___y_3237_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_3245_, lean_object* v_m_3246_, lean_object* v_a_3247_, lean_object* v_b_3248_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_m_3246_, v_a_3247_, v_b_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_3250_, lean_object* v_a_3251_, lean_object* v_x_3252_){
_start:
{
lean_object* v___x_3253_; 
v___x_3253_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_3251_, v_x_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_3254_, lean_object* v_a_3255_, lean_object* v_x_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_3254_, v_a_3255_, v_x_3256_);
lean_dec(v_x_3256_);
lean_dec_ref(v_a_3255_);
return v_res_3257_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_3258_, lean_object* v_a_3259_, lean_object* v_x_3260_){
_start:
{
uint8_t v___x_3261_; 
v___x_3261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_3259_, v_x_3260_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_3262_, lean_object* v_a_3263_, lean_object* v_x_3264_){
_start:
{
uint8_t v_res_3265_; lean_object* v_r_3266_; 
v_res_3265_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_3262_, v_a_3263_, v_x_3264_);
lean_dec(v_x_3264_);
lean_dec_ref(v_a_3263_);
v_r_3266_ = lean_box(v_res_3265_);
return v_r_3266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_3267_, lean_object* v_data_3268_){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_data_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_3270_, lean_object* v_a_3271_, lean_object* v_b_3272_, lean_object* v_x_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_3271_, v_b_3272_, v_x_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_3275_, lean_object* v_i_3276_, lean_object* v_source_3277_, lean_object* v_target_3278_){
_start:
{
lean_object* v___x_3279_; 
v___x_3279_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_3276_, v_source_3277_, v_target_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_3280_, lean_object* v_x_3281_, lean_object* v_x_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_3281_, v_x_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(lean_object* v_mvarId_3284_, lean_object* v_x_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3284_, v_x_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3294_ = v___x_3291_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3291_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3297_; 
if (v_isShared_3295_ == 0)
{
v___x_3297_ = v___x_3294_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3292_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
v_a_3300_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3291_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3291_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(lean_object* v_mvarId_3308_, lean_object* v_x_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3308_, v_x_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_object* v_00_u03b1_3316_, lean_object* v_mvarId_3317_, lean_object* v_x_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3317_, v_x_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(lean_object* v_00_u03b1_3325_, lean_object* v_mvarId_3326_, lean_object* v_x_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(v_00_u03b1_3325_, v_mvarId_3326_, v_x_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(uint8_t v_elimTrivial_3334_, lean_object* v_as_3335_, size_t v_sz_3336_, size_t v_i_3337_, lean_object* v_b_3338_){
_start:
{
uint8_t v___x_3340_; 
v___x_3340_ = lean_usize_dec_lt(v_i_3337_, v_sz_3336_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; 
v___x_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3341_, 0, v_b_3338_);
return v___x_3341_;
}
else
{
lean_object* v_snd_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3389_; 
v_snd_3342_ = lean_ctor_get(v_b_3338_, 1);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_b_3338_);
if (v_isSharedCheck_3389_ == 0)
{
lean_object* v_unused_3390_; 
v_unused_3390_ = lean_ctor_get(v_b_3338_, 0);
lean_dec(v_unused_3390_);
v___x_3344_ = v_b_3338_;
v_isShared_3345_ = v_isSharedCheck_3389_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_snd_3342_);
lean_dec(v_b_3338_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3389_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; lean_object* v_a_3348_; lean_object* v_a_3355_; 
v___x_3346_ = lean_box(0);
v_a_3355_ = lean_array_uget_borrowed(v_as_3335_, v_i_3337_);
if (lean_obj_tag(v_a_3355_) == 0)
{
v_a_3348_ = v_snd_3342_;
goto v___jp_3347_;
}
else
{
lean_object* v_val_3356_; lean_object* v_fst_3357_; lean_object* v_snd_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3388_; 
v_val_3356_ = lean_ctor_get(v_a_3355_, 0);
v_fst_3357_ = lean_ctor_get(v_snd_3342_, 0);
v_snd_3358_ = lean_ctor_get(v_snd_3342_, 1);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_snd_3342_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3360_ = v_snd_3342_;
v_isShared_3361_ = v_isSharedCheck_3388_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_snd_3358_);
lean_inc(v_fst_3357_);
lean_dec(v_snd_3342_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3388_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
uint8_t v___x_3362_; lean_object* v___x_3363_; 
v___x_3362_ = 0;
v___x_3363_ = l_Lean_LocalDecl_value_x3f(v_val_3356_, v___x_3362_);
if (lean_obj_tag(v___x_3363_) == 1)
{
lean_object* v_val_3364_; lean_object* v___x_3365_; 
v_val_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_val_3364_);
lean_dec_ref_known(v___x_3363_, 1);
v___x_3365_ = l_Lean_LocalDecl_type(v_val_3356_);
if (lean_obj_tag(v___x_3365_) == 10)
{
lean_object* v_data_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; uint8_t v___x_3371_; 
v_data_3366_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_data_3366_);
lean_dec_ref_known(v___x_3365_, 2);
v___x_3367_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3368_ = lean_unsigned_to_nat(2u);
v___x_3369_ = l_Lean_KVMap_getNat(v_data_3366_, v___x_3367_, v___x_3368_);
lean_dec(v_data_3366_);
v___x_3370_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3369_);
lean_dec(v___x_3369_);
v___x_3371_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3370_, v_val_3364_, v_elimTrivial_3334_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3372_ = l_Lean_LocalDecl_fvarId(v_val_3356_);
v___x_3373_ = l_Lean_mkFVar(v___x_3372_);
v___x_3374_ = lean_array_push(v_fst_3357_, v___x_3373_);
v___x_3375_ = lean_array_push(v_snd_3358_, v_val_3364_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 1, v___x_3375_);
lean_ctor_set(v___x_3360_, 0, v___x_3374_);
v___x_3377_ = v___x_3360_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3374_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
v_a_3348_ = v___x_3377_;
goto v___jp_3347_;
}
}
else
{
lean_object* v___x_3380_; 
lean_dec(v_val_3364_);
if (v_isShared_3361_ == 0)
{
v___x_3380_ = v___x_3360_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_fst_3357_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_snd_3358_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
v_a_3348_ = v___x_3380_;
goto v___jp_3347_;
}
}
}
else
{
lean_object* v___x_3383_; 
lean_dec_ref(v___x_3365_);
lean_dec(v_val_3364_);
if (v_isShared_3361_ == 0)
{
v___x_3383_ = v___x_3360_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_fst_3357_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v_snd_3358_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
v_a_3348_ = v___x_3383_;
goto v___jp_3347_;
}
}
}
else
{
lean_object* v___x_3386_; 
lean_dec(v___x_3363_);
if (v_isShared_3361_ == 0)
{
v___x_3386_ = v___x_3360_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_fst_3357_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_snd_3358_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
v_a_3348_ = v___x_3386_;
goto v___jp_3347_;
}
}
}
}
v___jp_3347_:
{
lean_object* v___x_3350_; 
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 1, v_a_3348_);
lean_ctor_set(v___x_3344_, 0, v___x_3346_);
v___x_3350_ = v___x_3344_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3346_);
lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_a_3348_);
v___x_3350_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
size_t v___x_3351_; size_t v___x_3352_; 
v___x_3351_ = ((size_t)1ULL);
v___x_3352_ = lean_usize_add(v_i_3337_, v___x_3351_);
v_i_3337_ = v___x_3352_;
v_b_3338_ = v___x_3350_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_elimTrivial_3391_, lean_object* v_as_3392_, lean_object* v_sz_3393_, lean_object* v_i_3394_, lean_object* v_b_3395_, lean_object* v___y_3396_){
_start:
{
uint8_t v_elimTrivial_boxed_3397_; size_t v_sz_boxed_3398_; size_t v_i_boxed_3399_; lean_object* v_res_3400_; 
v_elimTrivial_boxed_3397_ = lean_unbox(v_elimTrivial_3391_);
v_sz_boxed_3398_ = lean_unbox_usize(v_sz_3393_);
lean_dec(v_sz_3393_);
v_i_boxed_3399_ = lean_unbox_usize(v_i_3394_);
lean_dec(v_i_3394_);
v_res_3400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_boxed_3397_, v_as_3392_, v_sz_boxed_3398_, v_i_boxed_3399_, v_b_3395_);
lean_dec_ref(v_as_3392_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(uint8_t v_elimTrivial_3401_, lean_object* v_as_3402_, size_t v_sz_3403_, size_t v_i_3404_, lean_object* v_b_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
uint8_t v___x_3411_; 
v___x_3411_ = lean_usize_dec_lt(v_i_3404_, v_sz_3403_);
if (v___x_3411_ == 0)
{
lean_object* v___x_3412_; 
v___x_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3412_, 0, v_b_3405_);
return v___x_3412_;
}
else
{
lean_object* v_snd_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3460_; 
v_snd_3413_ = lean_ctor_get(v_b_3405_, 1);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_b_3405_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; 
v_unused_3461_ = lean_ctor_get(v_b_3405_, 0);
lean_dec(v_unused_3461_);
v___x_3415_ = v_b_3405_;
v_isShared_3416_ = v_isSharedCheck_3460_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_snd_3413_);
lean_dec(v_b_3405_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3460_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3417_; lean_object* v_a_3419_; lean_object* v_a_3426_; 
v___x_3417_ = lean_box(0);
v_a_3426_ = lean_array_uget_borrowed(v_as_3402_, v_i_3404_);
if (lean_obj_tag(v_a_3426_) == 0)
{
v_a_3419_ = v_snd_3413_;
goto v___jp_3418_;
}
else
{
lean_object* v_val_3427_; lean_object* v_fst_3428_; lean_object* v_snd_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3459_; 
v_val_3427_ = lean_ctor_get(v_a_3426_, 0);
v_fst_3428_ = lean_ctor_get(v_snd_3413_, 0);
v_snd_3429_ = lean_ctor_get(v_snd_3413_, 1);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_snd_3413_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3431_ = v_snd_3413_;
v_isShared_3432_ = v_isSharedCheck_3459_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_snd_3429_);
lean_inc(v_fst_3428_);
lean_dec(v_snd_3413_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3459_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
uint8_t v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = 0;
v___x_3434_ = l_Lean_LocalDecl_value_x3f(v_val_3427_, v___x_3433_);
if (lean_obj_tag(v___x_3434_) == 1)
{
lean_object* v_val_3435_; lean_object* v___x_3436_; 
v_val_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_val_3435_);
lean_dec_ref_known(v___x_3434_, 1);
v___x_3436_ = l_Lean_LocalDecl_type(v_val_3427_);
if (lean_obj_tag(v___x_3436_) == 10)
{
lean_object* v_data_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; uint8_t v___x_3441_; uint8_t v___x_3442_; 
v_data_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_data_3437_);
lean_dec_ref_known(v___x_3436_, 2);
v___x_3438_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3439_ = lean_unsigned_to_nat(2u);
v___x_3440_ = l_Lean_KVMap_getNat(v_data_3437_, v___x_3438_, v___x_3439_);
lean_dec(v_data_3437_);
v___x_3441_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3440_);
lean_dec(v___x_3440_);
v___x_3442_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3441_, v_val_3435_, v_elimTrivial_3401_);
if (v___x_3442_ == 0)
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3448_; 
v___x_3443_ = l_Lean_LocalDecl_fvarId(v_val_3427_);
v___x_3444_ = l_Lean_mkFVar(v___x_3443_);
v___x_3445_ = lean_array_push(v_fst_3428_, v___x_3444_);
v___x_3446_ = lean_array_push(v_snd_3429_, v_val_3435_);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 1, v___x_3446_);
lean_ctor_set(v___x_3431_, 0, v___x_3445_);
v___x_3448_ = v___x_3431_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
v_a_3419_ = v___x_3448_;
goto v___jp_3418_;
}
}
else
{
lean_object* v___x_3451_; 
lean_dec(v_val_3435_);
if (v_isShared_3432_ == 0)
{
v___x_3451_ = v___x_3431_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_fst_3428_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_snd_3429_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
v_a_3419_ = v___x_3451_;
goto v___jp_3418_;
}
}
}
else
{
lean_object* v___x_3454_; 
lean_dec_ref(v___x_3436_);
lean_dec(v_val_3435_);
if (v_isShared_3432_ == 0)
{
v___x_3454_ = v___x_3431_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_fst_3428_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_snd_3429_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
v_a_3419_ = v___x_3454_;
goto v___jp_3418_;
}
}
}
else
{
lean_object* v___x_3457_; 
lean_dec(v___x_3434_);
if (v_isShared_3432_ == 0)
{
v___x_3457_ = v___x_3431_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_fst_3428_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_snd_3429_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
v_a_3419_ = v___x_3457_;
goto v___jp_3418_;
}
}
}
}
v___jp_3418_:
{
lean_object* v___x_3421_; 
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 1, v_a_3419_);
lean_ctor_set(v___x_3415_, 0, v___x_3417_);
v___x_3421_ = v___x_3415_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3417_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_a_3419_);
v___x_3421_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
size_t v___x_3422_; size_t v___x_3423_; lean_object* v___x_3424_; 
v___x_3422_ = ((size_t)1ULL);
v___x_3423_ = lean_usize_add(v_i_3404_, v___x_3422_);
v___x_3424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_3401_, v_as_3402_, v_sz_3403_, v___x_3423_, v___x_3421_);
return v___x_3424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(lean_object* v_elimTrivial_3462_, lean_object* v_as_3463_, lean_object* v_sz_3464_, lean_object* v_i_3465_, lean_object* v_b_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
uint8_t v_elimTrivial_boxed_3472_; size_t v_sz_boxed_3473_; size_t v_i_boxed_3474_; lean_object* v_res_3475_; 
v_elimTrivial_boxed_3472_ = lean_unbox(v_elimTrivial_3462_);
v_sz_boxed_3473_ = lean_unbox_usize(v_sz_3464_);
lean_dec(v_sz_3464_);
v_i_boxed_3474_ = lean_unbox_usize(v_i_3465_);
lean_dec(v_i_3465_);
v_res_3475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_boxed_3472_, v_as_3463_, v_sz_boxed_3473_, v_i_boxed_3474_, v_b_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec_ref(v_as_3463_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(uint8_t v_elimTrivial_3476_, lean_object* v_as_3477_, size_t v_sz_3478_, size_t v_i_3479_, lean_object* v_b_3480_){
_start:
{
uint8_t v___x_3482_; 
v___x_3482_ = lean_usize_dec_lt(v_i_3479_, v_sz_3478_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3483_; 
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v_b_3480_);
return v___x_3483_;
}
else
{
lean_object* v_snd_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3531_; 
v_snd_3484_ = lean_ctor_get(v_b_3480_, 1);
v_isSharedCheck_3531_ = !lean_is_exclusive(v_b_3480_);
if (v_isSharedCheck_3531_ == 0)
{
lean_object* v_unused_3532_; 
v_unused_3532_ = lean_ctor_get(v_b_3480_, 0);
lean_dec(v_unused_3532_);
v___x_3486_ = v_b_3480_;
v_isShared_3487_ = v_isSharedCheck_3531_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_snd_3484_);
lean_dec(v_b_3480_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3531_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; lean_object* v_a_3490_; lean_object* v_a_3497_; 
v___x_3488_ = lean_box(0);
v_a_3497_ = lean_array_uget_borrowed(v_as_3477_, v_i_3479_);
if (lean_obj_tag(v_a_3497_) == 0)
{
v_a_3490_ = v_snd_3484_;
goto v___jp_3489_;
}
else
{
lean_object* v_val_3498_; lean_object* v_fst_3499_; lean_object* v_snd_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3530_; 
v_val_3498_ = lean_ctor_get(v_a_3497_, 0);
v_fst_3499_ = lean_ctor_get(v_snd_3484_, 0);
v_snd_3500_ = lean_ctor_get(v_snd_3484_, 1);
v_isSharedCheck_3530_ = !lean_is_exclusive(v_snd_3484_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3502_ = v_snd_3484_;
v_isShared_3503_ = v_isSharedCheck_3530_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_snd_3500_);
lean_inc(v_fst_3499_);
lean_dec(v_snd_3484_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3530_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
uint8_t v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = 0;
v___x_3505_ = l_Lean_LocalDecl_value_x3f(v_val_3498_, v___x_3504_);
if (lean_obj_tag(v___x_3505_) == 1)
{
lean_object* v_val_3506_; lean_object* v___x_3507_; 
v_val_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_val_3506_);
lean_dec_ref_known(v___x_3505_, 1);
v___x_3507_ = l_Lean_LocalDecl_type(v_val_3498_);
if (lean_obj_tag(v___x_3507_) == 10)
{
lean_object* v_data_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; uint8_t v___x_3512_; uint8_t v___x_3513_; 
v_data_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_data_3508_);
lean_dec_ref_known(v___x_3507_, 2);
v___x_3509_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3510_ = lean_unsigned_to_nat(2u);
v___x_3511_ = l_Lean_KVMap_getNat(v_data_3508_, v___x_3509_, v___x_3510_);
lean_dec(v_data_3508_);
v___x_3512_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3511_);
lean_dec(v___x_3511_);
v___x_3513_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3512_, v_val_3506_, v_elimTrivial_3476_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3519_; 
v___x_3514_ = l_Lean_LocalDecl_fvarId(v_val_3498_);
v___x_3515_ = l_Lean_mkFVar(v___x_3514_);
v___x_3516_ = lean_array_push(v_fst_3499_, v___x_3515_);
v___x_3517_ = lean_array_push(v_snd_3500_, v_val_3506_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 1, v___x_3517_);
lean_ctor_set(v___x_3502_, 0, v___x_3516_);
v___x_3519_ = v___x_3502_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3516_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
v_a_3490_ = v___x_3519_;
goto v___jp_3489_;
}
}
else
{
lean_object* v___x_3522_; 
lean_dec(v_val_3506_);
if (v_isShared_3503_ == 0)
{
v___x_3522_ = v___x_3502_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_fst_3499_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v_snd_3500_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
v_a_3490_ = v___x_3522_;
goto v___jp_3489_;
}
}
}
else
{
lean_object* v___x_3525_; 
lean_dec_ref(v___x_3507_);
lean_dec(v_val_3506_);
if (v_isShared_3503_ == 0)
{
v___x_3525_ = v___x_3502_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_fst_3499_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v_snd_3500_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
v_a_3490_ = v___x_3525_;
goto v___jp_3489_;
}
}
}
else
{
lean_object* v___x_3528_; 
lean_dec(v___x_3505_);
if (v_isShared_3503_ == 0)
{
v___x_3528_ = v___x_3502_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_fst_3499_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_snd_3500_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
v_a_3490_ = v___x_3528_;
goto v___jp_3489_;
}
}
}
}
v___jp_3489_:
{
lean_object* v___x_3492_; 
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 1, v_a_3490_);
lean_ctor_set(v___x_3486_, 0, v___x_3488_);
v___x_3492_ = v___x_3486_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3488_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_a_3490_);
v___x_3492_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
size_t v___x_3493_; size_t v___x_3494_; 
v___x_3493_ = ((size_t)1ULL);
v___x_3494_ = lean_usize_add(v_i_3479_, v___x_3493_);
v_i_3479_ = v___x_3494_;
v_b_3480_ = v___x_3492_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_elimTrivial_3533_, lean_object* v_as_3534_, lean_object* v_sz_3535_, lean_object* v_i_3536_, lean_object* v_b_3537_, lean_object* v___y_3538_){
_start:
{
uint8_t v_elimTrivial_boxed_3539_; size_t v_sz_boxed_3540_; size_t v_i_boxed_3541_; lean_object* v_res_3542_; 
v_elimTrivial_boxed_3539_ = lean_unbox(v_elimTrivial_3533_);
v_sz_boxed_3540_ = lean_unbox_usize(v_sz_3535_);
lean_dec(v_sz_3535_);
v_i_boxed_3541_ = lean_unbox_usize(v_i_3536_);
lean_dec(v_i_3536_);
v_res_3542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_boxed_3539_, v_as_3534_, v_sz_boxed_3540_, v_i_boxed_3541_, v_b_3537_);
lean_dec_ref(v_as_3534_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(uint8_t v_elimTrivial_3543_, lean_object* v_as_3544_, size_t v_sz_3545_, size_t v_i_3546_, lean_object* v_b_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
uint8_t v___x_3553_; 
v___x_3553_ = lean_usize_dec_lt(v_i_3546_, v_sz_3545_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; 
v___x_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3554_, 0, v_b_3547_);
return v___x_3554_;
}
else
{
lean_object* v_snd_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3602_; 
v_snd_3555_ = lean_ctor_get(v_b_3547_, 1);
v_isSharedCheck_3602_ = !lean_is_exclusive(v_b_3547_);
if (v_isSharedCheck_3602_ == 0)
{
lean_object* v_unused_3603_; 
v_unused_3603_ = lean_ctor_get(v_b_3547_, 0);
lean_dec(v_unused_3603_);
v___x_3557_ = v_b_3547_;
v_isShared_3558_ = v_isSharedCheck_3602_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_snd_3555_);
lean_dec(v_b_3547_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3602_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3559_; lean_object* v_a_3561_; lean_object* v_a_3568_; 
v___x_3559_ = lean_box(0);
v_a_3568_ = lean_array_uget_borrowed(v_as_3544_, v_i_3546_);
if (lean_obj_tag(v_a_3568_) == 0)
{
v_a_3561_ = v_snd_3555_;
goto v___jp_3560_;
}
else
{
lean_object* v_val_3569_; lean_object* v_fst_3570_; lean_object* v_snd_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3601_; 
v_val_3569_ = lean_ctor_get(v_a_3568_, 0);
v_fst_3570_ = lean_ctor_get(v_snd_3555_, 0);
v_snd_3571_ = lean_ctor_get(v_snd_3555_, 1);
v_isSharedCheck_3601_ = !lean_is_exclusive(v_snd_3555_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3573_ = v_snd_3555_;
v_isShared_3574_ = v_isSharedCheck_3601_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_snd_3571_);
lean_inc(v_fst_3570_);
lean_dec(v_snd_3555_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3601_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
uint8_t v___x_3575_; lean_object* v___x_3576_; 
v___x_3575_ = 0;
v___x_3576_ = l_Lean_LocalDecl_value_x3f(v_val_3569_, v___x_3575_);
if (lean_obj_tag(v___x_3576_) == 1)
{
lean_object* v_val_3577_; lean_object* v___x_3578_; 
v_val_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_val_3577_);
lean_dec_ref_known(v___x_3576_, 1);
v___x_3578_ = l_Lean_LocalDecl_type(v_val_3569_);
if (lean_obj_tag(v___x_3578_) == 10)
{
lean_object* v_data_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; uint8_t v___x_3583_; uint8_t v___x_3584_; 
v_data_3579_ = lean_ctor_get(v___x_3578_, 0);
lean_inc(v_data_3579_);
lean_dec_ref_known(v___x_3578_, 2);
v___x_3580_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3581_ = lean_unsigned_to_nat(2u);
v___x_3582_ = l_Lean_KVMap_getNat(v_data_3579_, v___x_3580_, v___x_3581_);
lean_dec(v_data_3579_);
v___x_3583_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3582_);
lean_dec(v___x_3582_);
v___x_3584_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3583_, v_val_3577_, v_elimTrivial_3543_);
if (v___x_3584_ == 0)
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3590_; 
v___x_3585_ = l_Lean_LocalDecl_fvarId(v_val_3569_);
v___x_3586_ = l_Lean_mkFVar(v___x_3585_);
v___x_3587_ = lean_array_push(v_fst_3570_, v___x_3586_);
v___x_3588_ = lean_array_push(v_snd_3571_, v_val_3577_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 1, v___x_3588_);
lean_ctor_set(v___x_3573_, 0, v___x_3587_);
v___x_3590_ = v___x_3573_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3587_);
lean_ctor_set(v_reuseFailAlloc_3591_, 1, v___x_3588_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
v_a_3561_ = v___x_3590_;
goto v___jp_3560_;
}
}
else
{
lean_object* v___x_3593_; 
lean_dec(v_val_3577_);
if (v_isShared_3574_ == 0)
{
v___x_3593_ = v___x_3573_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_fst_3570_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v_snd_3571_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
v_a_3561_ = v___x_3593_;
goto v___jp_3560_;
}
}
}
else
{
lean_object* v___x_3596_; 
lean_dec_ref(v___x_3578_);
lean_dec(v_val_3577_);
if (v_isShared_3574_ == 0)
{
v___x_3596_ = v___x_3573_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_fst_3570_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v_snd_3571_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
v_a_3561_ = v___x_3596_;
goto v___jp_3560_;
}
}
}
else
{
lean_object* v___x_3599_; 
lean_dec(v___x_3576_);
if (v_isShared_3574_ == 0)
{
v___x_3599_ = v___x_3573_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_fst_3570_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_snd_3571_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
v_a_3561_ = v___x_3599_;
goto v___jp_3560_;
}
}
}
}
v___jp_3560_:
{
lean_object* v___x_3563_; 
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 1, v_a_3561_);
lean_ctor_set(v___x_3557_, 0, v___x_3559_);
v___x_3563_ = v___x_3557_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3559_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_a_3561_);
v___x_3563_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
size_t v___x_3564_; size_t v___x_3565_; lean_object* v___x_3566_; 
v___x_3564_ = ((size_t)1ULL);
v___x_3565_ = lean_usize_add(v_i_3546_, v___x_3564_);
v___x_3566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_3543_, v_as_3544_, v_sz_3545_, v___x_3565_, v___x_3563_);
return v___x_3566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(lean_object* v_elimTrivial_3604_, lean_object* v_as_3605_, lean_object* v_sz_3606_, lean_object* v_i_3607_, lean_object* v_b_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
uint8_t v_elimTrivial_boxed_3614_; size_t v_sz_boxed_3615_; size_t v_i_boxed_3616_; lean_object* v_res_3617_; 
v_elimTrivial_boxed_3614_ = lean_unbox(v_elimTrivial_3604_);
v_sz_boxed_3615_ = lean_unbox_usize(v_sz_3606_);
lean_dec(v_sz_3606_);
v_i_boxed_3616_ = lean_unbox_usize(v_i_3607_);
lean_dec(v_i_3607_);
v_res_3617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_boxed_3614_, v_as_3605_, v_sz_boxed_3615_, v_i_boxed_3616_, v_b_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec_ref(v_as_3605_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(lean_object* v_init_3618_, uint8_t v_elimTrivial_3619_, lean_object* v_n_3620_, lean_object* v_b_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
if (lean_obj_tag(v_n_3620_) == 0)
{
lean_object* v_cs_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; size_t v_sz_3630_; size_t v___x_3631_; lean_object* v___x_3632_; 
v_cs_3627_ = lean_ctor_get(v_n_3620_, 0);
v___x_3628_ = lean_box(0);
v___x_3629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3628_);
lean_ctor_set(v___x_3629_, 1, v_b_3621_);
v_sz_3630_ = lean_array_size(v_cs_3627_);
v___x_3631_ = ((size_t)0ULL);
v___x_3632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3618_, v_elimTrivial_3619_, v_cs_3627_, v_sz_3630_, v___x_3631_, v___x_3629_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3647_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3635_ = v___x_3632_;
v_isShared_3636_ = v_isSharedCheck_3647_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3647_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v_fst_3637_; 
v_fst_3637_ = lean_ctor_get(v_a_3633_, 0);
if (lean_obj_tag(v_fst_3637_) == 0)
{
lean_object* v_snd_3638_; lean_object* v___x_3639_; lean_object* v___x_3641_; 
v_snd_3638_ = lean_ctor_get(v_a_3633_, 1);
lean_inc(v_snd_3638_);
lean_dec(v_a_3633_);
v___x_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3639_, 0, v_snd_3638_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v___x_3639_);
v___x_3641_ = v___x_3635_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3639_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
else
{
lean_object* v_val_3643_; lean_object* v___x_3645_; 
lean_inc_ref(v_fst_3637_);
lean_dec(v_a_3633_);
v_val_3643_ = lean_ctor_get(v_fst_3637_, 0);
lean_inc(v_val_3643_);
lean_dec_ref_known(v_fst_3637_, 1);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v_val_3643_);
v___x_3645_ = v___x_3635_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_val_3643_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
else
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
v_a_3648_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3632_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3632_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
}
else
{
lean_object* v_vs_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; size_t v_sz_3659_; size_t v___x_3660_; lean_object* v___x_3661_; 
v_vs_3656_ = lean_ctor_get(v_n_3620_, 0);
v___x_3657_ = lean_box(0);
v___x_3658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3657_);
lean_ctor_set(v___x_3658_, 1, v_b_3621_);
v_sz_3659_ = lean_array_size(v_vs_3656_);
v___x_3660_ = ((size_t)0ULL);
v___x_3661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_3619_, v_vs_3656_, v_sz_3659_, v___x_3660_, v___x_3658_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3676_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3664_ = v___x_3661_;
v_isShared_3665_ = v_isSharedCheck_3676_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3661_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3676_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v_fst_3666_; 
v_fst_3666_ = lean_ctor_get(v_a_3662_, 0);
if (lean_obj_tag(v_fst_3666_) == 0)
{
lean_object* v_snd_3667_; lean_object* v___x_3668_; lean_object* v___x_3670_; 
v_snd_3667_ = lean_ctor_get(v_a_3662_, 1);
lean_inc(v_snd_3667_);
lean_dec(v_a_3662_);
v___x_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3668_, 0, v_snd_3667_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v___x_3668_);
v___x_3670_ = v___x_3664_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3668_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
else
{
lean_object* v_val_3672_; lean_object* v___x_3674_; 
lean_inc_ref(v_fst_3666_);
lean_dec(v_a_3662_);
v_val_3672_ = lean_ctor_get(v_fst_3666_, 0);
lean_inc(v_val_3672_);
lean_dec_ref_known(v_fst_3666_, 1);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v_val_3672_);
v___x_3674_ = v___x_3664_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_val_3672_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
v_a_3677_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3661_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3661_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(lean_object* v_init_3685_, uint8_t v_elimTrivial_3686_, lean_object* v_as_3687_, size_t v_sz_3688_, size_t v_i_3689_, lean_object* v_b_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
uint8_t v___x_3696_; 
v___x_3696_ = lean_usize_dec_lt(v_i_3689_, v_sz_3688_);
if (v___x_3696_ == 0)
{
lean_object* v___x_3697_; 
v___x_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3697_, 0, v_b_3690_);
return v___x_3697_;
}
else
{
lean_object* v_snd_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3732_; 
v_snd_3698_ = lean_ctor_get(v_b_3690_, 1);
v_isSharedCheck_3732_ = !lean_is_exclusive(v_b_3690_);
if (v_isSharedCheck_3732_ == 0)
{
lean_object* v_unused_3733_; 
v_unused_3733_ = lean_ctor_get(v_b_3690_, 0);
lean_dec(v_unused_3733_);
v___x_3700_ = v_b_3690_;
v_isShared_3701_ = v_isSharedCheck_3732_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_snd_3698_);
lean_dec(v_b_3690_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3732_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3702_; lean_object* v_a_3703_; lean_object* v___x_3704_; 
v___x_3702_ = lean_box(0);
v_a_3703_ = lean_array_uget_borrowed(v_as_3687_, v_i_3689_);
lean_inc(v_snd_3698_);
v___x_3704_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3685_, v_elimTrivial_3686_, v_a_3703_, v_snd_3698_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3723_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3707_ = v___x_3704_;
v_isShared_3708_ = v_isSharedCheck_3723_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_a_3705_);
lean_dec(v___x_3704_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3723_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
if (lean_obj_tag(v_a_3705_) == 0)
{
lean_object* v___x_3709_; lean_object* v___x_3711_; 
v___x_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3709_, 0, v_a_3705_);
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 0, v___x_3709_);
v___x_3711_ = v___x_3700_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3709_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_snd_3698_);
v___x_3711_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
lean_object* v___x_3713_; 
if (v_isShared_3708_ == 0)
{
lean_ctor_set(v___x_3707_, 0, v___x_3711_);
v___x_3713_ = v___x_3707_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3711_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; 
lean_del_object(v___x_3707_);
lean_dec(v_snd_3698_);
v_a_3716_ = lean_ctor_get(v_a_3705_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v_a_3705_, 1);
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 1, v_a_3716_);
lean_ctor_set(v___x_3700_, 0, v___x_3702_);
v___x_3718_ = v___x_3700_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3702_);
lean_ctor_set(v_reuseFailAlloc_3722_, 1, v_a_3716_);
v___x_3718_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
size_t v___x_3719_; size_t v___x_3720_; 
v___x_3719_ = ((size_t)1ULL);
v___x_3720_ = lean_usize_add(v_i_3689_, v___x_3719_);
v_i_3689_ = v___x_3720_;
v_b_3690_ = v___x_3718_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_del_object(v___x_3700_);
lean_dec(v_snd_3698_);
v_a_3724_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3704_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3704_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(lean_object* v_init_3734_, lean_object* v_elimTrivial_3735_, lean_object* v_as_3736_, lean_object* v_sz_3737_, lean_object* v_i_3738_, lean_object* v_b_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
uint8_t v_elimTrivial_boxed_3745_; size_t v_sz_boxed_3746_; size_t v_i_boxed_3747_; lean_object* v_res_3748_; 
v_elimTrivial_boxed_3745_ = lean_unbox(v_elimTrivial_3735_);
v_sz_boxed_3746_ = lean_unbox_usize(v_sz_3737_);
lean_dec(v_sz_3737_);
v_i_boxed_3747_ = lean_unbox_usize(v_i_3738_);
lean_dec(v_i_3738_);
v_res_3748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3734_, v_elimTrivial_boxed_3745_, v_as_3736_, v_sz_boxed_3746_, v_i_boxed_3747_, v_b_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec_ref(v_as_3736_);
lean_dec_ref(v_init_3734_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(lean_object* v_init_3749_, lean_object* v_elimTrivial_3750_, lean_object* v_n_3751_, lean_object* v_b_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
uint8_t v_elimTrivial_boxed_3758_; lean_object* v_res_3759_; 
v_elimTrivial_boxed_3758_ = lean_unbox(v_elimTrivial_3750_);
v_res_3759_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3749_, v_elimTrivial_boxed_3758_, v_n_3751_, v_b_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec_ref(v_n_3751_);
lean_dec_ref(v_init_3749_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(uint8_t v_elimTrivial_3760_, lean_object* v_t_3761_, lean_object* v_init_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v_root_3768_; lean_object* v_tail_3769_; lean_object* v___x_3770_; 
v_root_3768_ = lean_ctor_get(v_t_3761_, 0);
v_tail_3769_ = lean_ctor_get(v_t_3761_, 1);
lean_inc_ref(v_init_3762_);
v___x_3770_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3762_, v_elimTrivial_3760_, v_root_3768_, v_init_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
lean_dec_ref(v_init_3762_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3807_; 
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3773_ = v___x_3770_;
v_isShared_3774_ = v_isSharedCheck_3807_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3770_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3807_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
if (lean_obj_tag(v_a_3771_) == 0)
{
lean_object* v_a_3775_; lean_object* v___x_3777_; 
v_a_3775_ = lean_ctor_get(v_a_3771_, 0);
lean_inc(v_a_3775_);
lean_dec_ref_known(v_a_3771_, 1);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 0, v_a_3775_);
v___x_3777_ = v___x_3773_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3775_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; size_t v_sz_3782_; size_t v___x_3783_; lean_object* v___x_3784_; 
lean_del_object(v___x_3773_);
v_a_3779_ = lean_ctor_get(v_a_3771_, 0);
lean_inc(v_a_3779_);
lean_dec_ref_known(v_a_3771_, 1);
v___x_3780_ = lean_box(0);
v___x_3781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3780_);
lean_ctor_set(v___x_3781_, 1, v_a_3779_);
v_sz_3782_ = lean_array_size(v_tail_3769_);
v___x_3783_ = ((size_t)0ULL);
v___x_3784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_3760_, v_tail_3769_, v_sz_3782_, v___x_3783_, v___x_3781_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3798_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3787_ = v___x_3784_;
v_isShared_3788_ = v_isSharedCheck_3798_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3784_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3798_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v_fst_3789_; 
v_fst_3789_ = lean_ctor_get(v_a_3785_, 0);
if (lean_obj_tag(v_fst_3789_) == 0)
{
lean_object* v_snd_3790_; lean_object* v___x_3792_; 
v_snd_3790_ = lean_ctor_get(v_a_3785_, 1);
lean_inc(v_snd_3790_);
lean_dec(v_a_3785_);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v_snd_3790_);
v___x_3792_ = v___x_3787_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_snd_3790_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
else
{
lean_object* v_val_3794_; lean_object* v___x_3796_; 
lean_inc_ref(v_fst_3789_);
lean_dec(v_a_3785_);
v_val_3794_ = lean_ctor_get(v_fst_3789_, 0);
lean_inc(v_val_3794_);
lean_dec_ref_known(v_fst_3789_, 1);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v_val_3794_);
v___x_3796_ = v___x_3787_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_val_3794_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
v_a_3799_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3784_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3784_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
v_a_3808_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3770_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3770_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(lean_object* v_elimTrivial_3816_, lean_object* v_t_3817_, lean_object* v_init_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
uint8_t v_elimTrivial_boxed_3824_; lean_object* v_res_3825_; 
v_elimTrivial_boxed_3824_ = lean_unbox(v_elimTrivial_3816_);
v_res_3825_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_boxed_3824_, v_t_3817_, v_init_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec_ref(v_t_3817_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(lean_object* v_as_3826_, size_t v_sz_3827_, size_t v_i_3828_, lean_object* v_b_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
uint8_t v___x_3835_; 
v___x_3835_ = lean_usize_dec_lt(v_i_3828_, v_sz_3827_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3836_; 
v___x_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3836_, 0, v_b_3829_);
return v___x_3836_;
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v_a_3837_ = lean_array_uget_borrowed(v_as_3826_, v_i_3828_);
v___x_3838_ = l_Lean_Expr_fvarId_x21(v_a_3837_);
v___x_3839_ = l_Lean_MVarId_tryClear(v_b_3829_, v___x_3838_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; size_t v___x_3841_; size_t v___x_3842_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_a_3840_);
lean_dec_ref_known(v___x_3839_, 1);
v___x_3841_ = ((size_t)1ULL);
v___x_3842_ = lean_usize_add(v_i_3828_, v___x_3841_);
v_i_3828_ = v___x_3842_;
v_b_3829_ = v_a_3840_;
goto _start;
}
else
{
return v___x_3839_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(lean_object* v_as_3844_, lean_object* v_sz_3845_, lean_object* v_i_3846_, lean_object* v_b_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
size_t v_sz_boxed_3853_; size_t v_i_boxed_3854_; lean_object* v_res_3855_; 
v_sz_boxed_3853_ = lean_unbox_usize(v_sz_3845_);
lean_dec(v_sz_3845_);
v_i_boxed_3854_ = lean_unbox_usize(v_i_3846_);
lean_dec(v_i_3846_);
v_res_3855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_as_3844_, v_sz_boxed_3853_, v_i_boxed_3854_, v_b_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec_ref(v_as_3844_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(lean_object* v_x_3856_, lean_object* v_x_3857_, lean_object* v_x_3858_, lean_object* v_x_3859_){
_start:
{
lean_object* v_ks_3860_; lean_object* v_vs_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3885_; 
v_ks_3860_ = lean_ctor_get(v_x_3856_, 0);
v_vs_3861_ = lean_ctor_get(v_x_3856_, 1);
v_isSharedCheck_3885_ = !lean_is_exclusive(v_x_3856_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3863_ = v_x_3856_;
v_isShared_3864_ = v_isSharedCheck_3885_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_vs_3861_);
lean_inc(v_ks_3860_);
lean_dec(v_x_3856_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3885_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3865_; uint8_t v___x_3866_; 
v___x_3865_ = lean_array_get_size(v_ks_3860_);
v___x_3866_ = lean_nat_dec_lt(v_x_3857_, v___x_3865_);
if (v___x_3866_ == 0)
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3870_; 
lean_dec(v_x_3857_);
v___x_3867_ = lean_array_push(v_ks_3860_, v_x_3858_);
v___x_3868_ = lean_array_push(v_vs_3861_, v_x_3859_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 1, v___x_3868_);
lean_ctor_set(v___x_3863_, 0, v___x_3867_);
v___x_3870_ = v___x_3863_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3867_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
else
{
lean_object* v_k_x27_3872_; uint8_t v___x_3873_; 
v_k_x27_3872_ = lean_array_fget_borrowed(v_ks_3860_, v_x_3857_);
v___x_3873_ = l_Lean_instBEqMVarId_beq(v_x_3858_, v_k_x27_3872_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3875_; 
if (v_isShared_3864_ == 0)
{
v___x_3875_ = v___x_3863_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_ks_3860_);
lean_ctor_set(v_reuseFailAlloc_3879_, 1, v_vs_3861_);
v___x_3875_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3876_ = lean_unsigned_to_nat(1u);
v___x_3877_ = lean_nat_add(v_x_3857_, v___x_3876_);
lean_dec(v_x_3857_);
v_x_3856_ = v___x_3875_;
v_x_3857_ = v___x_3877_;
goto _start;
}
}
else
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3883_; 
v___x_3880_ = lean_array_fset(v_ks_3860_, v_x_3857_, v_x_3858_);
v___x_3881_ = lean_array_fset(v_vs_3861_, v_x_3857_, v_x_3859_);
lean_dec(v_x_3857_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 1, v___x_3881_);
lean_ctor_set(v___x_3863_, 0, v___x_3880_);
v___x_3883_ = v___x_3863_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v___x_3880_);
lean_ctor_set(v_reuseFailAlloc_3884_, 1, v___x_3881_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(lean_object* v_n_3886_, lean_object* v_k_3887_, lean_object* v_v_3888_){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = lean_unsigned_to_nat(0u);
v___x_3890_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_n_3886_, v___x_3889_, v_k_3887_, v_v_3888_);
return v___x_3890_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3891_; 
v___x_3891_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(lean_object* v_x_3892_, size_t v_x_3893_, size_t v_x_3894_, lean_object* v_x_3895_, lean_object* v_x_3896_){
_start:
{
if (lean_obj_tag(v_x_3892_) == 0)
{
lean_object* v_es_3897_; size_t v___x_3898_; size_t v___x_3899_; lean_object* v_j_3900_; lean_object* v___x_3901_; uint8_t v___x_3902_; 
v_es_3897_ = lean_ctor_get(v_x_3892_, 0);
v___x_3898_ = ((size_t)31ULL);
v___x_3899_ = lean_usize_land(v_x_3893_, v___x_3898_);
v_j_3900_ = lean_usize_to_nat(v___x_3899_);
v___x_3901_ = lean_array_get_size(v_es_3897_);
v___x_3902_ = lean_nat_dec_lt(v_j_3900_, v___x_3901_);
if (v___x_3902_ == 0)
{
lean_dec(v_j_3900_);
lean_dec(v_x_3896_);
lean_dec(v_x_3895_);
return v_x_3892_;
}
else
{
lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3941_; 
lean_inc_ref(v_es_3897_);
v_isSharedCheck_3941_ = !lean_is_exclusive(v_x_3892_);
if (v_isSharedCheck_3941_ == 0)
{
lean_object* v_unused_3942_; 
v_unused_3942_ = lean_ctor_get(v_x_3892_, 0);
lean_dec(v_unused_3942_);
v___x_3904_ = v_x_3892_;
v_isShared_3905_ = v_isSharedCheck_3941_;
goto v_resetjp_3903_;
}
else
{
lean_dec(v_x_3892_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3941_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v_v_3906_; lean_object* v___x_3907_; lean_object* v_xs_x27_3908_; lean_object* v___y_3910_; 
v_v_3906_ = lean_array_fget(v_es_3897_, v_j_3900_);
v___x_3907_ = lean_box(0);
v_xs_x27_3908_ = lean_array_fset(v_es_3897_, v_j_3900_, v___x_3907_);
switch(lean_obj_tag(v_v_3906_))
{
case 0:
{
lean_object* v_key_3915_; lean_object* v_val_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3926_; 
v_key_3915_ = lean_ctor_get(v_v_3906_, 0);
v_val_3916_ = lean_ctor_get(v_v_3906_, 1);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_v_3906_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3918_ = v_v_3906_;
v_isShared_3919_ = v_isSharedCheck_3926_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_val_3916_);
lean_inc(v_key_3915_);
lean_dec(v_v_3906_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3926_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
uint8_t v___x_3920_; 
v___x_3920_ = l_Lean_instBEqMVarId_beq(v_x_3895_, v_key_3915_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
lean_del_object(v___x_3918_);
v___x_3921_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3915_, v_val_3916_, v_x_3895_, v_x_3896_);
v___x_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
v___y_3910_ = v___x_3922_;
goto v___jp_3909_;
}
else
{
lean_object* v___x_3924_; 
lean_dec(v_val_3916_);
lean_dec(v_key_3915_);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 1, v_x_3896_);
lean_ctor_set(v___x_3918_, 0, v_x_3895_);
v___x_3924_ = v___x_3918_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_x_3895_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v_x_3896_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
v___y_3910_ = v___x_3924_;
goto v___jp_3909_;
}
}
}
}
case 1:
{
lean_object* v_node_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3939_; 
v_node_3927_ = lean_ctor_get(v_v_3906_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v_v_3906_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3929_ = v_v_3906_;
v_isShared_3930_ = v_isSharedCheck_3939_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_node_3927_);
lean_dec(v_v_3906_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3939_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
size_t v___x_3931_; size_t v___x_3932_; size_t v___x_3933_; size_t v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3937_; 
v___x_3931_ = ((size_t)5ULL);
v___x_3932_ = lean_usize_shift_right(v_x_3893_, v___x_3931_);
v___x_3933_ = ((size_t)1ULL);
v___x_3934_ = lean_usize_add(v_x_3894_, v___x_3933_);
v___x_3935_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_node_3927_, v___x_3932_, v___x_3934_, v_x_3895_, v_x_3896_);
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 0, v___x_3935_);
v___x_3937_ = v___x_3929_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
v___y_3910_ = v___x_3937_;
goto v___jp_3909_;
}
}
}
default: 
{
lean_object* v___x_3940_; 
v___x_3940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3940_, 0, v_x_3895_);
lean_ctor_set(v___x_3940_, 1, v_x_3896_);
v___y_3910_ = v___x_3940_;
goto v___jp_3909_;
}
}
v___jp_3909_:
{
lean_object* v___x_3911_; lean_object* v___x_3913_; 
v___x_3911_ = lean_array_fset(v_xs_x27_3908_, v_j_3900_, v___y_3910_);
lean_dec(v_j_3900_);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 0, v___x_3911_);
v___x_3913_ = v___x_3904_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
}
else
{
lean_object* v_ks_3943_; lean_object* v_vs_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3962_; 
v_ks_3943_ = lean_ctor_get(v_x_3892_, 0);
v_vs_3944_ = lean_ctor_get(v_x_3892_, 1);
v_isSharedCheck_3962_ = !lean_is_exclusive(v_x_3892_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3946_ = v_x_3892_;
v_isShared_3947_ = v_isSharedCheck_3962_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_vs_3944_);
lean_inc(v_ks_3943_);
lean_dec(v_x_3892_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3962_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3949_; 
if (v_isShared_3947_ == 0)
{
v___x_3949_ = v___x_3946_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_ks_3943_);
lean_ctor_set(v_reuseFailAlloc_3961_, 1, v_vs_3944_);
v___x_3949_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
lean_object* v_newNode_3950_; size_t v___x_3951_; uint8_t v___x_3952_; 
v_newNode_3950_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v___x_3949_, v_x_3895_, v_x_3896_);
v___x_3951_ = ((size_t)7ULL);
v___x_3952_ = lean_usize_dec_le(v___x_3951_, v_x_3894_);
if (v___x_3952_ == 0)
{
lean_object* v___x_3953_; lean_object* v___x_3954_; uint8_t v___x_3955_; 
v___x_3953_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3950_);
v___x_3954_ = lean_unsigned_to_nat(4u);
v___x_3955_ = lean_nat_dec_lt(v___x_3953_, v___x_3954_);
lean_dec(v___x_3953_);
if (v___x_3955_ == 0)
{
lean_object* v_ks_3956_; lean_object* v_vs_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v_ks_3956_ = lean_ctor_get(v_newNode_3950_, 0);
lean_inc_ref(v_ks_3956_);
v_vs_3957_ = lean_ctor_get(v_newNode_3950_, 1);
lean_inc_ref(v_vs_3957_);
lean_dec_ref(v_newNode_3950_);
v___x_3958_ = lean_unsigned_to_nat(0u);
v___x_3959_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0);
v___x_3960_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_x_3894_, v_ks_3956_, v_vs_3957_, v___x_3958_, v___x_3959_);
lean_dec_ref(v_vs_3957_);
lean_dec_ref(v_ks_3956_);
return v___x_3960_;
}
else
{
return v_newNode_3950_;
}
}
else
{
return v_newNode_3950_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(size_t v_depth_3963_, lean_object* v_keys_3964_, lean_object* v_vals_3965_, lean_object* v_i_3966_, lean_object* v_entries_3967_){
_start:
{
lean_object* v___x_3968_; uint8_t v___x_3969_; 
v___x_3968_ = lean_array_get_size(v_keys_3964_);
v___x_3969_ = lean_nat_dec_lt(v_i_3966_, v___x_3968_);
if (v___x_3969_ == 0)
{
lean_dec(v_i_3966_);
return v_entries_3967_;
}
else
{
lean_object* v_k_3970_; lean_object* v_v_3971_; uint64_t v___x_3972_; size_t v_h_3973_; size_t v___x_3974_; lean_object* v___x_3975_; size_t v___x_3976_; size_t v___x_3977_; size_t v___x_3978_; size_t v_h_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v_k_3970_ = lean_array_fget_borrowed(v_keys_3964_, v_i_3966_);
v_v_3971_ = lean_array_fget_borrowed(v_vals_3965_, v_i_3966_);
v___x_3972_ = l_Lean_instHashableMVarId_hash(v_k_3970_);
v_h_3973_ = lean_uint64_to_usize(v___x_3972_);
v___x_3974_ = ((size_t)5ULL);
v___x_3975_ = lean_unsigned_to_nat(1u);
v___x_3976_ = ((size_t)1ULL);
v___x_3977_ = lean_usize_sub(v_depth_3963_, v___x_3976_);
v___x_3978_ = lean_usize_mul(v___x_3974_, v___x_3977_);
v_h_3979_ = lean_usize_shift_right(v_h_3973_, v___x_3978_);
v___x_3980_ = lean_nat_add(v_i_3966_, v___x_3975_);
lean_dec(v_i_3966_);
lean_inc(v_v_3971_);
lean_inc(v_k_3970_);
v___x_3981_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_entries_3967_, v_h_3979_, v_depth_3963_, v_k_3970_, v_v_3971_);
v_i_3966_ = v___x_3980_;
v_entries_3967_ = v___x_3981_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_depth_3983_, lean_object* v_keys_3984_, lean_object* v_vals_3985_, lean_object* v_i_3986_, lean_object* v_entries_3987_){
_start:
{
size_t v_depth_boxed_3988_; lean_object* v_res_3989_; 
v_depth_boxed_3988_ = lean_unbox_usize(v_depth_3983_);
lean_dec(v_depth_3983_);
v_res_3989_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_boxed_3988_, v_keys_3984_, v_vals_3985_, v_i_3986_, v_entries_3987_);
lean_dec_ref(v_vals_3985_);
lean_dec_ref(v_keys_3984_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_x_3990_, lean_object* v_x_3991_, lean_object* v_x_3992_, lean_object* v_x_3993_, lean_object* v_x_3994_){
_start:
{
size_t v_x_7807__boxed_3995_; size_t v_x_7808__boxed_3996_; lean_object* v_res_3997_; 
v_x_7807__boxed_3995_ = lean_unbox_usize(v_x_3991_);
lean_dec(v_x_3991_);
v_x_7808__boxed_3996_ = lean_unbox_usize(v_x_3992_);
lean_dec(v_x_3992_);
v_res_3997_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_3990_, v_x_7807__boxed_3995_, v_x_7808__boxed_3996_, v_x_3993_, v_x_3994_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(lean_object* v_x_3998_, lean_object* v_x_3999_, lean_object* v_x_4000_){
_start:
{
uint64_t v___x_4001_; size_t v___x_4002_; size_t v___x_4003_; lean_object* v___x_4004_; 
v___x_4001_ = l_Lean_instHashableMVarId_hash(v_x_3999_);
v___x_4002_ = lean_uint64_to_usize(v___x_4001_);
v___x_4003_ = ((size_t)1ULL);
v___x_4004_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_3998_, v___x_4002_, v___x_4003_, v_x_3999_, v_x_4000_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(lean_object* v_mvarId_4005_, lean_object* v_val_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v___x_4009_; lean_object* v_mctx_4010_; lean_object* v_cache_4011_; lean_object* v_zetaDeltaFVarIds_4012_; lean_object* v_postponed_4013_; lean_object* v_diag_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4043_; 
v___x_4009_ = lean_st_ref_take(v___y_4007_);
v_mctx_4010_ = lean_ctor_get(v___x_4009_, 0);
v_cache_4011_ = lean_ctor_get(v___x_4009_, 1);
v_zetaDeltaFVarIds_4012_ = lean_ctor_get(v___x_4009_, 2);
v_postponed_4013_ = lean_ctor_get(v___x_4009_, 3);
v_diag_4014_ = lean_ctor_get(v___x_4009_, 4);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4016_ = v___x_4009_;
v_isShared_4017_ = v_isSharedCheck_4043_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_diag_4014_);
lean_inc(v_postponed_4013_);
lean_inc(v_zetaDeltaFVarIds_4012_);
lean_inc(v_cache_4011_);
lean_inc(v_mctx_4010_);
lean_dec(v___x_4009_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4043_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v_depth_4018_; lean_object* v_levelAssignDepth_4019_; lean_object* v_lmvarCounter_4020_; lean_object* v_mvarCounter_4021_; lean_object* v_lDecls_4022_; lean_object* v_decls_4023_; lean_object* v_userNames_4024_; lean_object* v_lAssignment_4025_; lean_object* v_eAssignment_4026_; lean_object* v_dAssignment_4027_; lean_object* v_instanceTypedMVars_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4042_; 
v_depth_4018_ = lean_ctor_get(v_mctx_4010_, 0);
v_levelAssignDepth_4019_ = lean_ctor_get(v_mctx_4010_, 1);
v_lmvarCounter_4020_ = lean_ctor_get(v_mctx_4010_, 2);
v_mvarCounter_4021_ = lean_ctor_get(v_mctx_4010_, 3);
v_lDecls_4022_ = lean_ctor_get(v_mctx_4010_, 4);
v_decls_4023_ = lean_ctor_get(v_mctx_4010_, 5);
v_userNames_4024_ = lean_ctor_get(v_mctx_4010_, 6);
v_lAssignment_4025_ = lean_ctor_get(v_mctx_4010_, 7);
v_eAssignment_4026_ = lean_ctor_get(v_mctx_4010_, 8);
v_dAssignment_4027_ = lean_ctor_get(v_mctx_4010_, 9);
v_instanceTypedMVars_4028_ = lean_ctor_get(v_mctx_4010_, 10);
v_isSharedCheck_4042_ = !lean_is_exclusive(v_mctx_4010_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4030_ = v_mctx_4010_;
v_isShared_4031_ = v_isSharedCheck_4042_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_instanceTypedMVars_4028_);
lean_inc(v_dAssignment_4027_);
lean_inc(v_eAssignment_4026_);
lean_inc(v_lAssignment_4025_);
lean_inc(v_userNames_4024_);
lean_inc(v_decls_4023_);
lean_inc(v_lDecls_4022_);
lean_inc(v_mvarCounter_4021_);
lean_inc(v_lmvarCounter_4020_);
lean_inc(v_levelAssignDepth_4019_);
lean_inc(v_depth_4018_);
lean_dec(v_mctx_4010_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4042_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4035_; 
v___x_4032_ = lean_box(0);
v___x_4033_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_eAssignment_4026_, v_mvarId_4005_, v_val_4006_);
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 8, v___x_4033_);
v___x_4035_ = v___x_4030_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_depth_4018_);
lean_ctor_set(v_reuseFailAlloc_4041_, 1, v_levelAssignDepth_4019_);
lean_ctor_set(v_reuseFailAlloc_4041_, 2, v_lmvarCounter_4020_);
lean_ctor_set(v_reuseFailAlloc_4041_, 3, v_mvarCounter_4021_);
lean_ctor_set(v_reuseFailAlloc_4041_, 4, v_lDecls_4022_);
lean_ctor_set(v_reuseFailAlloc_4041_, 5, v_decls_4023_);
lean_ctor_set(v_reuseFailAlloc_4041_, 6, v_userNames_4024_);
lean_ctor_set(v_reuseFailAlloc_4041_, 7, v_lAssignment_4025_);
lean_ctor_set(v_reuseFailAlloc_4041_, 8, v___x_4033_);
lean_ctor_set(v_reuseFailAlloc_4041_, 9, v_dAssignment_4027_);
lean_ctor_set(v_reuseFailAlloc_4041_, 10, v_instanceTypedMVars_4028_);
v___x_4035_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
lean_object* v___x_4037_; 
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v___x_4035_);
v___x_4037_ = v___x_4016_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4035_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v_cache_4011_);
lean_ctor_set(v_reuseFailAlloc_4040_, 2, v_zetaDeltaFVarIds_4012_);
lean_ctor_set(v_reuseFailAlloc_4040_, 3, v_postponed_4013_);
lean_ctor_set(v_reuseFailAlloc_4040_, 4, v_diag_4014_);
v___x_4037_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4038_ = lean_st_ref_put(v___y_4007_, v___x_4037_);
v___x_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4032_);
return v___x_4039_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(lean_object* v_mvarId_4044_, lean_object* v_val_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v_res_4048_; 
v_res_4048_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4044_, v_val_4045_, v___y_4046_);
lean_dec(v___y_4046_);
return v_res_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0(lean_object* v_mvar_4051_, uint8_t v_elimTrivial_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
lean_object* v_lctx_4058_; lean_object* v___x_4059_; 
v_lctx_4058_ = lean_ctor_get(v___y_4053_, 2);
lean_inc(v_mvar_4051_);
v___x_4059_ = l_Lean_MVarId_getType(v_mvar_4051_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v_a_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
lean_inc(v_a_4060_);
lean_dec_ref_known(v___x_4059_, 1);
v___x_4061_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_4062_ = l_Lean_Elab_Tactic_Do_countUses(v_a_4060_, v___x_4061_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; lean_object* v_fst_4064_; lean_object* v_snd_4065_; lean_object* v___x_4066_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_a_4063_);
lean_dec_ref_known(v___x_4062_, 1);
v_fst_4064_ = lean_ctor_get(v_a_4063_, 0);
lean_inc(v_fst_4064_);
v_snd_4065_ = lean_ctor_get(v_a_4063_, 1);
lean_inc(v_snd_4065_);
lean_dec(v_a_4063_);
lean_inc_ref(v_lctx_4058_);
v___x_4066_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_lctx_4058_, v_snd_4065_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; lean_object* v___x_4068_; lean_object* v_decls_4069_; lean_object* v___x_4070_; 
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_a_4067_);
lean_dec_ref_known(v___x_4066_, 1);
v___x_4068_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0));
v_decls_4069_ = lean_ctor_get(v_a_4067_, 1);
lean_inc_ref(v_decls_4069_);
lean_dec(v_a_4067_);
v___x_4070_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_4052_, v_decls_4069_, v___x_4068_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
lean_dec_ref(v_decls_4069_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_a_4071_; lean_object* v_fst_4072_; lean_object* v_snd_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4070_, 1);
v_fst_4072_ = lean_ctor_get(v_a_4071_, 0);
lean_inc(v_fst_4072_);
v_snd_4073_ = lean_ctor_get(v_a_4071_, 1);
lean_inc(v_snd_4073_);
lean_dec(v_a_4071_);
v___x_4074_ = l_Lean_Expr_replaceFVars(v_fst_4064_, v_fst_4072_, v_snd_4073_);
lean_dec(v_snd_4073_);
lean_dec(v_fst_4064_);
v___x_4075_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v___x_4074_, v_elimTrivial_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v___x_4077_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_a_4076_);
lean_dec_ref_known(v___x_4075_, 1);
lean_inc(v_mvar_4051_);
v___x_4077_ = l_Lean_MVarId_getTag(v_mvar_4051_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4079_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
lean_inc(v_a_4078_);
lean_dec_ref_known(v___x_4077_, 1);
v___x_4079_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4076_, v_a_4078_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; size_t v_sz_4083_; size_t v___x_4084_; lean_object* v___x_4085_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc_n(v_a_4080_, 2);
lean_dec_ref_known(v___x_4079_, 1);
v___x_4081_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvar_4051_, v_a_4080_, v___y_4054_);
lean_dec_ref(v___x_4081_);
v___x_4082_ = l_Lean_Expr_mvarId_x21(v_a_4080_);
lean_dec(v_a_4080_);
v_sz_4083_ = lean_array_size(v_fst_4072_);
v___x_4084_ = ((size_t)0ULL);
v___x_4085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_fst_4072_, v_sz_4083_, v___x_4084_, v___x_4082_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
lean_dec_ref(v___y_4053_);
lean_dec(v_fst_4072_);
return v___x_4085_;
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4093_; 
lean_dec(v_fst_4072_);
lean_dec_ref(v___y_4053_);
lean_dec(v_mvar_4051_);
v_a_4086_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4088_ = v___x_4079_;
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v___x_4079_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4093_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4091_; 
if (v_isShared_4089_ == 0)
{
v___x_4091_ = v___x_4088_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4086_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
else
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4101_; 
lean_dec(v_a_4076_);
lean_dec(v_fst_4072_);
lean_dec_ref(v___y_4053_);
lean_dec(v_mvar_4051_);
v_a_4094_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4096_ = v___x_4077_;
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4077_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4099_; 
if (v_isShared_4097_ == 0)
{
v___x_4099_ = v___x_4096_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_4094_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
}
}
}
}
else
{
lean_object* v_a_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4109_; 
lean_dec(v_fst_4072_);
lean_dec_ref(v___y_4053_);
lean_dec(v_mvar_4051_);
v_a_4102_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4104_ = v___x_4075_;
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_a_4102_);
lean_dec(v___x_4075_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4107_; 
if (v_isShared_4105_ == 0)
{
v___x_4107_ = v___x_4104_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_a_4102_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
}
}
else
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4117_; 
lean_dec(v_fst_4064_);
lean_dec_ref(v___y_4053_);
lean_dec(v_mvar_4051_);
v_a_4110_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4112_ = v___x_4070_;
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v___x_4070_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4115_; 
if (v_isShared_4113_ == 0)
{
v___x_4115_ = v___x_4112_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4110_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
lean_dec(v_fst_4064_);
lean_dec_ref(v___y_4053_);
lean_dec(v_mvar_4051_);
v_a_4118_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v___x_4066_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4066_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
else
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4133_; 
lean_dec_ref(v___y_4053_);
lean_dec(v_mvar_4051_);
v_a_4126_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4128_ = v___x_4062_;
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4062_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4126_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
lean_dec_ref(v___y_4053_);
lean_dec(v_mvar_4051_);
v_a_4134_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4059_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4059_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(lean_object* v_mvar_4142_, lean_object* v_elimTrivial_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
uint8_t v_elimTrivial_boxed_4149_; lean_object* v_res_4150_; 
v_elimTrivial_boxed_4149_ = lean_unbox(v_elimTrivial_4143_);
v_res_4150_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0(v_mvar_4142_, v_elimTrivial_boxed_4149_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v___y_4145_);
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets(lean_object* v_mvar_4151_, uint8_t v_elimTrivial_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_){
_start:
{
lean_object* v___x_4158_; lean_object* v___f_4159_; lean_object* v___x_4160_; 
v___x_4158_ = lean_box(v_elimTrivial_4152_);
lean_inc(v_mvar_4151_);
v___f_4159_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4159_, 0, v_mvar_4151_);
lean_closure_set(v___f_4159_, 1, v___x_4158_);
v___x_4160_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvar_4151_, v___f_4159_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___boxed(lean_object* v_mvar_4161_, lean_object* v_elimTrivial_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_){
_start:
{
uint8_t v_elimTrivial_boxed_4168_; lean_object* v_res_4169_; 
v_elimTrivial_boxed_4168_ = lean_unbox(v_elimTrivial_4162_);
v_res_4169_ = l_Lean_Elab_Tactic_Do_elimLets(v_mvar_4161_, v_elimTrivial_boxed_4168_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
lean_dec(v_a_4166_);
lean_dec_ref(v_a_4165_);
lean_dec(v_a_4164_);
lean_dec_ref(v_a_4163_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(lean_object* v_mvarId_4170_, lean_object* v_val_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
lean_object* v___x_4177_; 
v___x_4177_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4170_, v_val_4171_, v___y_4173_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(lean_object* v_mvarId_4178_, lean_object* v_val_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(v_mvarId_4178_, v_val_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(lean_object* v_00_u03b2_4186_, lean_object* v_x_4187_, lean_object* v_x_4188_, lean_object* v_x_4189_){
_start:
{
lean_object* v___x_4190_; 
v___x_4190_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_x_4187_, v_x_4188_, v_x_4189_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(uint8_t v_elimTrivial_4191_, lean_object* v_as_4192_, size_t v_sz_4193_, size_t v_i_4194_, lean_object* v_b_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v___x_4201_; 
v___x_4201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_4191_, v_as_4192_, v_sz_4193_, v_i_4194_, v_b_4195_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(lean_object* v_elimTrivial_4202_, lean_object* v_as_4203_, lean_object* v_sz_4204_, lean_object* v_i_4205_, lean_object* v_b_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
uint8_t v_elimTrivial_boxed_4212_; size_t v_sz_boxed_4213_; size_t v_i_boxed_4214_; lean_object* v_res_4215_; 
v_elimTrivial_boxed_4212_ = lean_unbox(v_elimTrivial_4202_);
v_sz_boxed_4213_ = lean_unbox_usize(v_sz_4204_);
lean_dec(v_sz_4204_);
v_i_boxed_4214_ = lean_unbox_usize(v_i_4205_);
lean_dec(v_i_4205_);
v_res_4215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(v_elimTrivial_boxed_4212_, v_as_4203_, v_sz_boxed_4213_, v_i_boxed_4214_, v_b_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec_ref(v_as_4203_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_4216_, lean_object* v_x_4217_, size_t v_x_4218_, size_t v_x_4219_, lean_object* v_x_4220_, lean_object* v_x_4221_){
_start:
{
lean_object* v___x_4222_; 
v___x_4222_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4217_, v_x_4218_, v_x_4219_, v_x_4220_, v_x_4221_);
return v___x_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_4223_, lean_object* v_x_4224_, lean_object* v_x_4225_, lean_object* v_x_4226_, lean_object* v_x_4227_, lean_object* v_x_4228_){
_start:
{
size_t v_x_8253__boxed_4229_; size_t v_x_8254__boxed_4230_; lean_object* v_res_4231_; 
v_x_8253__boxed_4229_ = lean_unbox_usize(v_x_4225_);
lean_dec(v_x_4225_);
v_x_8254__boxed_4230_ = lean_unbox_usize(v_x_4226_);
lean_dec(v_x_4226_);
v_res_4231_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(v_00_u03b2_4223_, v_x_4224_, v_x_8253__boxed_4229_, v_x_8254__boxed_4230_, v_x_4227_, v_x_4228_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(uint8_t v_elimTrivial_4232_, lean_object* v_as_4233_, size_t v_sz_4234_, size_t v_i_4235_, lean_object* v_b_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v___x_4242_; 
v___x_4242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_4232_, v_as_4233_, v_sz_4234_, v_i_4235_, v_b_4236_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(lean_object* v_elimTrivial_4243_, lean_object* v_as_4244_, lean_object* v_sz_4245_, lean_object* v_i_4246_, lean_object* v_b_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
uint8_t v_elimTrivial_boxed_4253_; size_t v_sz_boxed_4254_; size_t v_i_boxed_4255_; lean_object* v_res_4256_; 
v_elimTrivial_boxed_4253_ = lean_unbox(v_elimTrivial_4243_);
v_sz_boxed_4254_ = lean_unbox_usize(v_sz_4245_);
lean_dec(v_sz_4245_);
v_i_boxed_4255_ = lean_unbox_usize(v_i_4246_);
lean_dec(v_i_4246_);
v_res_4256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(v_elimTrivial_boxed_4253_, v_as_4244_, v_sz_boxed_4254_, v_i_boxed_4255_, v_b_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec_ref(v_as_4244_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(lean_object* v_00_u03b2_4257_, lean_object* v_n_4258_, lean_object* v_k_4259_, lean_object* v_v_4260_){
_start:
{
lean_object* v___x_4261_; 
v___x_4261_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v_n_4258_, v_k_4259_, v_v_4260_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_4262_, size_t v_depth_4263_, lean_object* v_keys_4264_, lean_object* v_vals_4265_, lean_object* v_heq_4266_, lean_object* v_i_4267_, lean_object* v_entries_4268_){
_start:
{
lean_object* v___x_4269_; 
v___x_4269_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_4263_, v_keys_4264_, v_vals_4265_, v_i_4267_, v_entries_4268_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_4270_, lean_object* v_depth_4271_, lean_object* v_keys_4272_, lean_object* v_vals_4273_, lean_object* v_heq_4274_, lean_object* v_i_4275_, lean_object* v_entries_4276_){
_start:
{
size_t v_depth_boxed_4277_; lean_object* v_res_4278_; 
v_depth_boxed_4277_ = lean_unbox_usize(v_depth_4271_);
lean_dec(v_depth_4271_);
v_res_4278_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_4270_, v_depth_boxed_4277_, v_keys_4272_, v_vals_4273_, v_heq_4274_, v_i_4275_, v_entries_4276_);
lean_dec_ref(v_vals_4273_);
lean_dec_ref(v_keys_4272_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_4279_, lean_object* v_x_4280_, lean_object* v_x_4281_, lean_object* v_x_4282_, lean_object* v_x_4283_){
_start:
{
lean_object* v___x_4284_; 
v___x_4284_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_x_4280_, v_x_4281_, v_x_4282_, v_x_4283_);
return v___x_4284_;
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
