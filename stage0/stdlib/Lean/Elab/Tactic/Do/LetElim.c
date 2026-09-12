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
lean_object* v___x_745_; lean_object* v_ngen_746_; lean_object* v_namePrefix_747_; lean_object* v_idx_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_777_; 
v___x_745_ = lean_st_ref_get(v___y_743_);
v_ngen_746_ = lean_ctor_get(v___x_745_, 2);
lean_inc_ref(v_ngen_746_);
lean_dec(v___x_745_);
v_namePrefix_747_ = lean_ctor_get(v_ngen_746_, 0);
v_idx_748_ = lean_ctor_get(v_ngen_746_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v_ngen_746_);
if (v_isSharedCheck_777_ == 0)
{
v___x_750_ = v_ngen_746_;
v_isShared_751_ = v_isSharedCheck_777_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_idx_748_);
lean_inc(v_namePrefix_747_);
lean_dec(v_ngen_746_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_777_;
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
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_namePrefix_747_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_754_);
v___x_756_ = v_reuseFailAlloc_776_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v_env_758_; lean_object* v_nextMacroScope_759_; lean_object* v_auxDeclNGen_760_; lean_object* v_traceState_761_; lean_object* v_cache_762_; lean_object* v_messages_763_; lean_object* v_infoState_764_; lean_object* v_snapshotTasks_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_774_; 
v___x_757_ = lean_st_ref_take(v___y_743_);
v_env_758_ = lean_ctor_get(v___x_757_, 0);
v_nextMacroScope_759_ = lean_ctor_get(v___x_757_, 1);
v_auxDeclNGen_760_ = lean_ctor_get(v___x_757_, 3);
v_traceState_761_ = lean_ctor_get(v___x_757_, 4);
v_cache_762_ = lean_ctor_get(v___x_757_, 5);
v_messages_763_ = lean_ctor_get(v___x_757_, 6);
v_infoState_764_ = lean_ctor_get(v___x_757_, 7);
v_snapshotTasks_765_ = lean_ctor_get(v___x_757_, 8);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v___x_757_, 2);
lean_dec(v_unused_775_);
v___x_767_ = v___x_757_;
v_isShared_768_ = v_isSharedCheck_774_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_snapshotTasks_765_);
lean_inc(v_infoState_764_);
lean_inc(v_messages_763_);
lean_inc(v_cache_762_);
lean_inc(v_traceState_761_);
lean_inc(v_auxDeclNGen_760_);
lean_inc(v_nextMacroScope_759_);
lean_inc(v_env_758_);
lean_dec(v___x_757_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_774_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 2, v___x_756_);
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_env_758_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_nextMacroScope_759_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_773_, 3, v_auxDeclNGen_760_);
lean_ctor_set(v_reuseFailAlloc_773_, 4, v_traceState_761_);
lean_ctor_set(v_reuseFailAlloc_773_, 5, v_cache_762_);
lean_ctor_set(v_reuseFailAlloc_773_, 6, v_messages_763_);
lean_ctor_set(v_reuseFailAlloc_773_, 7, v_infoState_764_);
lean_ctor_set(v_reuseFailAlloc_773_, 8, v_snapshotTasks_765_);
v___x_770_ = v_reuseFailAlloc_773_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_st_ref_put(v___y_743_, v___x_770_);
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v_r_752_);
return v___x_772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg___boxed(lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_778_);
lean_dec(v___y_778_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_786_; lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
v___x_786_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_784_);
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5___boxed(lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v___y_795_, v___y_796_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(lean_object* v_a_801_, lean_object* v_x_802_){
_start:
{
if (lean_obj_tag(v_x_802_) == 0)
{
return v_x_802_;
}
else
{
lean_object* v_key_803_; lean_object* v_value_804_; lean_object* v_tail_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_814_; 
v_key_803_ = lean_ctor_get(v_x_802_, 0);
v_value_804_ = lean_ctor_get(v_x_802_, 1);
v_tail_805_ = lean_ctor_get(v_x_802_, 2);
v_isSharedCheck_814_ = !lean_is_exclusive(v_x_802_);
if (v_isSharedCheck_814_ == 0)
{
v___x_807_ = v_x_802_;
v_isShared_808_ = v_isSharedCheck_814_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_tail_805_);
lean_inc(v_value_804_);
lean_inc(v_key_803_);
lean_dec(v_x_802_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_814_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
uint8_t v___x_809_; 
v___x_809_ = l_Lean_instBEqFVarId_beq(v_key_803_, v_a_801_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_801_, v_tail_805_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 2, v___x_810_);
v___x_812_ = v___x_807_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_key_803_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_value_804_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
else
{
lean_del_object(v___x_807_);
lean_dec(v_value_804_);
lean_dec(v_key_803_);
return v_tail_805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(lean_object* v_a_815_, lean_object* v_x_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_815_, v_x_816_);
lean_dec(v_a_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(lean_object* v_m_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_size_820_; lean_object* v_buckets_821_; lean_object* v___x_822_; uint64_t v___x_823_; uint64_t v___x_824_; uint64_t v___x_825_; uint64_t v_fold_826_; uint64_t v___x_827_; uint64_t v___x_828_; uint64_t v___x_829_; size_t v___x_830_; size_t v___x_831_; size_t v___x_832_; size_t v___x_833_; size_t v___x_834_; lean_object* v_bkt_835_; uint8_t v___x_836_; 
v_size_820_ = lean_ctor_get(v_m_818_, 0);
v_buckets_821_ = lean_ctor_get(v_m_818_, 1);
v___x_822_ = lean_array_get_size(v_buckets_821_);
v___x_823_ = l_Lean_instHashableFVarId_hash(v_a_819_);
v___x_824_ = 32ULL;
v___x_825_ = lean_uint64_shift_right(v___x_823_, v___x_824_);
v_fold_826_ = lean_uint64_xor(v___x_823_, v___x_825_);
v___x_827_ = 16ULL;
v___x_828_ = lean_uint64_shift_right(v_fold_826_, v___x_827_);
v___x_829_ = lean_uint64_xor(v_fold_826_, v___x_828_);
v___x_830_ = lean_uint64_to_usize(v___x_829_);
v___x_831_ = lean_usize_of_nat(v___x_822_);
v___x_832_ = ((size_t)1ULL);
v___x_833_ = lean_usize_sub(v___x_831_, v___x_832_);
v___x_834_ = lean_usize_land(v___x_830_, v___x_833_);
v_bkt_835_ = lean_array_uget_borrowed(v_buckets_821_, v___x_834_);
v___x_836_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_819_, v_bkt_835_);
if (v___x_836_ == 0)
{
return v_m_818_;
}
else
{
lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_849_; 
lean_inc(v_bkt_835_);
lean_inc_ref(v_buckets_821_);
lean_inc(v_size_820_);
v_isSharedCheck_849_ = !lean_is_exclusive(v_m_818_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; lean_object* v_unused_851_; 
v_unused_850_ = lean_ctor_get(v_m_818_, 1);
lean_dec(v_unused_850_);
v_unused_851_ = lean_ctor_get(v_m_818_, 0);
lean_dec(v_unused_851_);
v___x_838_ = v_m_818_;
v_isShared_839_ = v_isSharedCheck_849_;
goto v_resetjp_837_;
}
else
{
lean_dec(v_m_818_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_849_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v_buckets_x27_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_840_ = lean_box(0);
v_buckets_x27_841_ = lean_array_uset(v_buckets_821_, v___x_834_, v___x_840_);
v___x_842_ = lean_unsigned_to_nat(1u);
v___x_843_ = lean_nat_sub(v_size_820_, v___x_842_);
lean_dec(v_size_820_);
v___x_844_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_819_, v_bkt_835_);
v___x_845_ = lean_array_uset(v_buckets_x27_841_, v___x_834_, v___x_844_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v___x_845_);
lean_ctor_set(v___x_838_, 0, v___x_843_);
v___x_847_ = v___x_838_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(lean_object* v_m_852_, lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_852_, v_a_853_);
lean_dec(v_a_853_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(lean_object* v_a_855_, lean_object* v_fallback_856_, lean_object* v_x_857_){
_start:
{
if (lean_obj_tag(v_x_857_) == 0)
{
lean_inc(v_fallback_856_);
return v_fallback_856_;
}
else
{
lean_object* v_key_858_; lean_object* v_value_859_; lean_object* v_tail_860_; uint8_t v___x_861_; 
v_key_858_ = lean_ctor_get(v_x_857_, 0);
v_value_859_ = lean_ctor_get(v_x_857_, 1);
v_tail_860_ = lean_ctor_get(v_x_857_, 2);
v___x_861_ = l_Lean_instBEqFVarId_beq(v_key_858_, v_a_855_);
if (v___x_861_ == 0)
{
v_x_857_ = v_tail_860_;
goto _start;
}
else
{
lean_inc(v_value_859_);
return v_value_859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(lean_object* v_a_863_, lean_object* v_fallback_864_, lean_object* v_x_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_863_, v_fallback_864_, v_x_865_);
lean_dec(v_x_865_);
lean_dec(v_fallback_864_);
lean_dec(v_a_863_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(lean_object* v_m_867_, lean_object* v_a_868_, lean_object* v_fallback_869_){
_start:
{
lean_object* v_buckets_870_; lean_object* v___x_871_; uint64_t v___x_872_; uint64_t v___x_873_; uint64_t v___x_874_; uint64_t v_fold_875_; uint64_t v___x_876_; uint64_t v___x_877_; uint64_t v___x_878_; size_t v___x_879_; size_t v___x_880_; size_t v___x_881_; size_t v___x_882_; size_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_buckets_870_ = lean_ctor_get(v_m_867_, 1);
v___x_871_ = lean_array_get_size(v_buckets_870_);
v___x_872_ = l_Lean_instHashableFVarId_hash(v_a_868_);
v___x_873_ = 32ULL;
v___x_874_ = lean_uint64_shift_right(v___x_872_, v___x_873_);
v_fold_875_ = lean_uint64_xor(v___x_872_, v___x_874_);
v___x_876_ = 16ULL;
v___x_877_ = lean_uint64_shift_right(v_fold_875_, v___x_876_);
v___x_878_ = lean_uint64_xor(v_fold_875_, v___x_877_);
v___x_879_ = lean_uint64_to_usize(v___x_878_);
v___x_880_ = lean_usize_of_nat(v___x_871_);
v___x_881_ = ((size_t)1ULL);
v___x_882_ = lean_usize_sub(v___x_880_, v___x_881_);
v___x_883_ = lean_usize_land(v___x_879_, v___x_882_);
v___x_884_ = lean_array_uget_borrowed(v_buckets_870_, v___x_883_);
v___x_885_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_868_, v_fallback_869_, v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(lean_object* v_m_886_, lean_object* v_a_887_, lean_object* v_fallback_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_886_, v_a_887_, v_fallback_888_);
lean_dec(v_fallback_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_m_886_);
return v_res_889_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = lean_box(0);
v___x_895_ = lean_unsigned_to_nat(16u);
v___x_896_ = lean_mk_array(v___x_895_, v___x_894_);
return v___x_896_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v___x_897_);
return v___x_899_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__1(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__0));
v___x_902_ = l_Lean_stringToMessageData(v___x_901_);
return v___x_902_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__3(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__2));
v___x_905_ = l_Lean_stringToMessageData(v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__5(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__4));
v___x_908_ = l_Lean_stringToMessageData(v___x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses(lean_object* v_e_909_, lean_object* v_subst_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
switch(lean_obj_tag(v_e_909_))
{
case 0:
{
lean_object* v_deBruijnIndex_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_deBruijnIndex_916_ = lean_ctor_get(v_e_909_, 0);
v___x_917_ = lean_array_get_size(v_subst_910_);
v___x_918_ = lean_nat_dec_lt(v_deBruijnIndex_916_, v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_inc(v_deBruijnIndex_916_);
lean_dec_ref_known(v_e_909_, 1);
lean_dec_ref(v_subst_910_);
v___x_919_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__1, &l_Lean_Elab_Tactic_Do_countUses___closed__1_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__1);
v___x_920_ = l_Nat_reprFast(v_deBruijnIndex_916_);
v___x_921_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
v___x_922_ = l_Lean_MessageData_ofFormat(v___x_921_);
v___x_923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_919_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__3, &l_Lean_Elab_Tactic_Do_countUses___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__3);
v___x_925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = l_Nat_reprFast(v___x_917_);
v___x_927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
v___x_928_ = l_Lean_MessageData_ofFormat(v___x_927_);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_925_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_929_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_931_ = lean_unsigned_to_nat(1u);
v___x_932_ = lean_nat_sub(v___x_917_, v___x_931_);
v___x_933_ = lean_nat_sub(v___x_932_, v_deBruijnIndex_916_);
lean_dec(v___x_932_);
v___x_934_ = lean_array_fget(v_subst_910_, v___x_933_);
lean_dec(v___x_933_);
lean_dec_ref(v_subst_910_);
v___x_935_ = 1;
v___x_936_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_937_ = lean_box(v___x_935_);
v___x_938_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_936_, v___x_934_, v___x_937_);
v___x_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_939_, 0, v_e_909_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
}
case 1:
{
lean_object* v_fvarId_941_; uint8_t v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec_ref(v_subst_910_);
v_fvarId_941_ = lean_ctor_get(v_e_909_, 0);
v___x_942_ = 1;
v___x_943_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_944_ = lean_box(v___x_942_);
lean_inc(v_fvarId_941_);
v___x_945_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_943_, v_fvarId_941_, v___x_944_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v_e_909_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
case 5:
{
lean_object* v_fn_948_; lean_object* v_arg_949_; lean_object* v___x_950_; 
v_fn_948_ = lean_ctor_get(v_e_909_, 0);
lean_inc_ref(v_fn_948_);
v_arg_949_ = lean_ctor_get(v_e_909_, 1);
lean_inc_ref(v_arg_949_);
lean_dec_ref_known(v_e_909_, 2);
lean_inc_ref(v_subst_910_);
v___x_950_ = l_Lean_Elab_Tactic_Do_countUses(v_fn_948_, v_subst_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v_fst_952_; lean_object* v_snd_953_; lean_object* v___x_954_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
v_fst_952_ = lean_ctor_get(v_a_951_, 0);
lean_inc(v_fst_952_);
v_snd_953_ = lean_ctor_get(v_a_951_, 1);
lean_inc(v_snd_953_);
lean_dec(v_a_951_);
v___x_954_ = l_Lean_Elab_Tactic_Do_countUses(v_arg_949_, v_subst_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_973_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_973_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_973_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_973_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_fst_959_; lean_object* v_snd_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_972_; 
v_fst_959_ = lean_ctor_get(v_a_955_, 0);
v_snd_960_ = lean_ctor_get(v_a_955_, 1);
v_isSharedCheck_972_ = !lean_is_exclusive(v_a_955_);
if (v_isSharedCheck_972_ == 0)
{
v___x_962_ = v_a_955_;
v_isShared_963_ = v_isSharedCheck_972_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_snd_960_);
lean_inc(v_fst_959_);
lean_dec(v_a_955_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_972_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_964_ = l_Lean_Expr_app___override(v_fst_952_, v_fst_959_);
v___x_965_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_953_, v_snd_960_);
lean_dec(v_snd_953_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v___x_965_);
lean_ctor_set(v___x_962_, 0, v___x_964_);
v___x_967_ = v___x_962_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v___x_965_);
v___x_967_ = v_reuseFailAlloc_971_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_969_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_967_);
v___x_969_ = v___x_957_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
else
{
lean_dec(v_snd_953_);
lean_dec(v_fst_952_);
return v___x_954_;
}
}
else
{
lean_dec_ref(v_arg_949_);
lean_dec_ref(v_subst_910_);
return v___x_950_;
}
}
case 6:
{
lean_object* v_binderName_974_; lean_object* v_binderType_975_; lean_object* v_body_976_; uint8_t v_binderInfo_977_; lean_object* v___x_978_; 
v_binderName_974_ = lean_ctor_get(v_e_909_, 0);
lean_inc(v_binderName_974_);
v_binderType_975_ = lean_ctor_get(v_e_909_, 1);
lean_inc_ref(v_binderType_975_);
v_body_976_ = lean_ctor_get(v_e_909_, 2);
lean_inc_ref(v_body_976_);
v_binderInfo_977_ = lean_ctor_get_uint8(v_e_909_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_909_, 3);
v___x_978_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
lean_inc_ref(v_subst_910_);
v___x_980_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_975_, v_subst_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v_fst_982_; lean_object* v_snd_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
v_fst_982_ = lean_ctor_get(v_a_981_, 0);
lean_inc(v_fst_982_);
v_snd_983_ = lean_ctor_get(v_a_981_, 1);
lean_inc(v_snd_983_);
lean_dec(v_a_981_);
lean_inc(v_a_979_);
v___x_984_ = lean_array_push(v_subst_910_, v_a_979_);
v___x_985_ = l_Lean_Elab_Tactic_Do_countUses(v_body_976_, v___x_984_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1005_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_1005_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1005_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v_fst_990_; lean_object* v_snd_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1004_; 
v_fst_990_ = lean_ctor_get(v_a_986_, 0);
v_snd_991_ = lean_ctor_get(v_a_986_, 1);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_a_986_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_993_ = v_a_986_;
v_isShared_994_ = v_isSharedCheck_1004_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_snd_991_);
lean_inc(v_fst_990_);
lean_dec(v_a_986_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1004_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_995_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_983_, v_snd_991_);
lean_dec(v_snd_983_);
v___x_996_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_995_, v_a_979_);
lean_dec(v_a_979_);
v___x_997_ = l_Lean_Expr_lam___override(v_binderName_974_, v_fst_982_, v_fst_990_, v_binderInfo_977_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v___x_996_);
lean_ctor_set(v___x_993_, 0, v___x_997_);
v___x_999_ = v___x_993_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v___x_996_);
v___x_999_ = v_reuseFailAlloc_1003_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1001_; 
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_999_);
v___x_1001_ = v___x_988_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
}
else
{
lean_dec(v_snd_983_);
lean_dec(v_fst_982_);
lean_dec(v_a_979_);
lean_dec(v_binderName_974_);
return v___x_985_;
}
}
else
{
lean_dec(v_a_979_);
lean_dec_ref(v_body_976_);
lean_dec(v_binderName_974_);
lean_dec_ref(v_subst_910_);
return v___x_980_;
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec_ref(v_body_976_);
lean_dec_ref(v_binderType_975_);
lean_dec(v_binderName_974_);
lean_dec_ref(v_subst_910_);
v_a_1006_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_978_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_978_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1014_; lean_object* v_binderType_1015_; lean_object* v_body_1016_; uint8_t v_binderInfo_1017_; lean_object* v___x_1018_; 
v_binderName_1014_ = lean_ctor_get(v_e_909_, 0);
lean_inc(v_binderName_1014_);
v_binderType_1015_ = lean_ctor_get(v_e_909_, 1);
lean_inc_ref(v_binderType_1015_);
v_body_1016_ = lean_ctor_get(v_e_909_, 2);
lean_inc_ref(v_body_1016_);
v_binderInfo_1017_ = lean_ctor_get_uint8(v_e_909_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_909_, 3);
v___x_1018_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
lean_inc_ref(v_subst_910_);
v___x_1020_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_1015_, v_subst_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v_fst_1022_; lean_object* v_snd_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v_fst_1022_ = lean_ctor_get(v_a_1021_, 0);
lean_inc(v_fst_1022_);
v_snd_1023_ = lean_ctor_get(v_a_1021_, 1);
lean_inc(v_snd_1023_);
lean_dec(v_a_1021_);
lean_inc(v_a_1019_);
v___x_1024_ = lean_array_push(v_subst_910_, v_a_1019_);
v___x_1025_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1016_, v___x_1024_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1045_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1045_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1045_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v_fst_1030_; lean_object* v_snd_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1044_; 
v_fst_1030_ = lean_ctor_get(v_a_1026_, 0);
v_snd_1031_ = lean_ctor_get(v_a_1026_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_a_1026_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1033_ = v_a_1026_;
v_isShared_1034_ = v_isSharedCheck_1044_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_snd_1031_);
lean_inc(v_fst_1030_);
lean_dec(v_a_1026_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1044_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1035_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_1023_, v_snd_1031_);
lean_dec(v_snd_1023_);
v___x_1036_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_1035_, v_a_1019_);
lean_dec(v_a_1019_);
v___x_1037_ = l_Lean_Expr_forallE___override(v_binderName_1014_, v_fst_1022_, v_fst_1030_, v_binderInfo_1017_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 1, v___x_1036_);
lean_ctor_set(v___x_1033_, 0, v___x_1037_);
v___x_1039_ = v___x_1033_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v___x_1036_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1039_);
v___x_1041_ = v___x_1028_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
else
{
lean_dec(v_snd_1023_);
lean_dec(v_fst_1022_);
lean_dec(v_a_1019_);
lean_dec(v_binderName_1014_);
return v___x_1025_;
}
}
else
{
lean_dec(v_a_1019_);
lean_dec_ref(v_body_1016_);
lean_dec(v_binderName_1014_);
lean_dec_ref(v_subst_910_);
return v___x_1020_;
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec_ref(v_body_1016_);
lean_dec_ref(v_binderType_1015_);
lean_dec(v_binderName_1014_);
lean_dec_ref(v_subst_910_);
v_a_1046_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1018_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1018_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
case 8:
{
lean_object* v_declName_1054_; lean_object* v_type_1055_; lean_object* v_value_1056_; lean_object* v_body_1057_; uint8_t v_nondep_1058_; lean_object* v___x_1059_; 
v_declName_1054_ = lean_ctor_get(v_e_909_, 0);
lean_inc(v_declName_1054_);
v_type_1055_ = lean_ctor_get(v_e_909_, 1);
lean_inc_ref(v_type_1055_);
v_value_1056_ = lean_ctor_get(v_e_909_, 2);
lean_inc_ref(v_value_1056_);
v_body_1057_ = lean_ctor_get(v_e_909_, 3);
lean_inc_ref(v_body_1057_);
v_nondep_1058_ = lean_ctor_get_uint8(v_e_909_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_909_, 4);
v___x_1059_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc_n(v_a_1060_, 2);
lean_dec_ref_known(v___x_1059_, 1);
lean_inc_ref(v_subst_910_);
v___x_1061_ = lean_array_push(v_subst_910_, v_a_1060_);
v___x_1062_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1057_, v___x_1061_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1105_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1105_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1105_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v_fst_1067_; lean_object* v_snd_1068_; lean_object* v___x_1070_; 
v_fst_1067_ = lean_ctor_get(v_a_1063_, 0);
lean_inc(v_fst_1067_);
v_snd_1068_ = lean_ctor_get(v_a_1063_, 1);
lean_inc(v_snd_1068_);
lean_dec(v_a_1063_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set_tag(v___x_1065_, 1);
lean_ctor_set(v___x_1065_, 0, v_value_1056_);
v___x_1070_ = v___x_1065_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_value_1056_);
v___x_1070_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_a_1060_, v_type_1055_, v___x_1070_, v_snd_1068_, v_subst_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
lean_dec(v_a_1060_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1095_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1095_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1095_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v_snd_1076_; lean_object* v_fst_1077_; 
v_snd_1076_ = lean_ctor_get(v_a_1072_, 1);
lean_inc(v_snd_1076_);
v_fst_1077_ = lean_ctor_get(v_snd_1076_, 0);
lean_inc(v_fst_1077_);
if (lean_obj_tag(v_fst_1077_) == 1)
{
lean_object* v_fst_1078_; lean_object* v_snd_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1091_; 
v_fst_1078_ = lean_ctor_get(v_a_1072_, 0);
lean_inc(v_fst_1078_);
lean_dec(v_a_1072_);
v_snd_1079_ = lean_ctor_get(v_snd_1076_, 1);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_snd_1076_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v_snd_1076_, 0);
lean_dec(v_unused_1092_);
v___x_1081_ = v_snd_1076_;
v_isShared_1082_ = v_isSharedCheck_1091_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_snd_1079_);
lean_dec(v_snd_1076_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1091_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v_val_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v_val_1083_ = lean_ctor_get(v_fst_1077_, 0);
lean_inc(v_val_1083_);
lean_dec_ref_known(v_fst_1077_, 1);
v___x_1084_ = l_Lean_Expr_letE___override(v_declName_1054_, v_fst_1078_, v_val_1083_, v_fst_1067_, v_nondep_1058_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1084_);
v___x_1086_ = v___x_1081_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_snd_1079_);
v___x_1086_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1088_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1086_);
v___x_1088_ = v___x_1074_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_dec(v_fst_1077_);
lean_dec(v_snd_1076_);
lean_del_object(v___x_1074_);
lean_dec(v_a_1072_);
lean_dec(v_fst_1067_);
lean_dec(v_declName_1054_);
v___x_1093_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__5, &l_Lean_Elab_Tactic_Do_countUses___closed__5_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__5);
v___x_1094_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_1093_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
return v___x_1094_;
}
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec(v_fst_1067_);
lean_dec(v_declName_1054_);
v_a_1096_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1071_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1071_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1060_);
lean_dec_ref(v_value_1056_);
lean_dec_ref(v_type_1055_);
lean_dec(v_declName_1054_);
lean_dec_ref(v_subst_910_);
return v___x_1062_;
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v_body_1057_);
lean_dec_ref(v_value_1056_);
lean_dec_ref(v_type_1055_);
lean_dec(v_declName_1054_);
lean_dec_ref(v_subst_910_);
v_a_1106_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1059_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1059_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
case 10:
{
lean_object* v_data_1114_; lean_object* v_expr_1115_; lean_object* v___f_1116_; lean_object* v___x_1117_; 
v_data_1114_ = lean_ctor_get(v_e_909_, 0);
lean_inc(v_data_1114_);
v_expr_1115_ = lean_ctor_get(v_e_909_, 1);
lean_inc_ref(v_expr_1115_);
lean_dec_ref_known(v_e_909_, 2);
v___f_1116_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__0), 2, 1);
lean_closure_set(v___f_1116_, 0, v_data_1114_);
v___x_1117_ = l_Lean_Elab_Tactic_Do_countUses(v_expr_1115_, v_subst_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1126_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1122_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1116_, v_a_1118_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1122_);
v___x_1124_ = v___x_1120_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
else
{
lean_dec_ref(v___f_1116_);
return v___x_1117_;
}
}
case 11:
{
lean_object* v_typeName_1127_; lean_object* v_idx_1128_; lean_object* v_struct_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; 
v_typeName_1127_ = lean_ctor_get(v_e_909_, 0);
lean_inc(v_typeName_1127_);
v_idx_1128_ = lean_ctor_get(v_e_909_, 1);
lean_inc(v_idx_1128_);
v_struct_1129_ = lean_ctor_get(v_e_909_, 2);
lean_inc_ref(v_struct_1129_);
lean_dec_ref_known(v_e_909_, 3);
v___f_1130_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__1), 3, 2);
lean_closure_set(v___f_1130_, 0, v_typeName_1127_);
lean_closure_set(v___f_1130_, 1, v_idx_1128_);
v___x_1131_ = l_Lean_Elab_Tactic_Do_countUses(v_struct_1129_, v_subst_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1140_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1140_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1140_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1136_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1130_, v_a_1132_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1136_);
v___x_1138_ = v___x_1134_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
else
{
lean_dec_ref(v___f_1130_);
return v___x_1131_;
}
}
default: 
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec_ref(v_subst_910_);
v___x_1141_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v_e_909_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
return v___x_1143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl(lean_object* v_fvarId_1144_, lean_object* v_ty_1145_, lean_object* v_val_x3f_1146_, lean_object* v_bodyUses_1147_, lean_object* v_subst_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v___f_1154_; lean_object* v___x_1155_; 
v___f_1154_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0));
lean_inc_ref(v_subst_1148_);
v___x_1155_ = l_Lean_Elab_Tactic_Do_countUses(v_ty_1145_, v_subst_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1210_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1210_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1210_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v_fst_1160_; lean_object* v_snd_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1209_; 
v_fst_1160_ = lean_ctor_get(v_a_1156_, 0);
v_snd_1161_ = lean_ctor_get(v_a_1156_, 1);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_a_1156_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1163_ = v_a_1156_;
v_isShared_1164_ = v_isSharedCheck_1209_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_snd_1161_);
lean_inc(v_fst_1160_);
lean_dec(v_a_1156_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1209_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___y_1166_; uint8_t v___y_1167_; lean_object* v___y_1168_; lean_object* v_fst_1183_; lean_object* v_snd_1184_; 
if (lean_obj_tag(v_val_x3f_1146_) == 0)
{
lean_object* v___x_1194_; 
lean_dec_ref(v_subst_1148_);
v___x_1194_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v_fst_1183_ = v_val_x3f_1146_;
v_snd_1184_ = v___x_1194_;
goto v___jp_1182_;
}
else
{
lean_object* v_val_1195_; lean_object* v___x_1196_; 
v_val_1195_ = lean_ctor_get(v_val_x3f_1146_, 0);
lean_inc(v_val_1195_);
lean_dec_ref_known(v_val_x3f_1146_, 1);
v___x_1196_ = l_Lean_Elab_Tactic_Do_countUses(v_val_1195_, v_subst_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1198_; lean_object* v_fst_1199_; lean_object* v_snd_1200_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref_known(v___x_1196_, 1);
v___x_1198_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1154_, v_a_1197_);
v_fst_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_fst_1199_);
v_snd_1200_ = lean_ctor_get(v___x_1198_, 1);
lean_inc(v_snd_1200_);
lean_dec_ref(v___x_1198_);
v_fst_1183_ = v_fst_1199_;
v_snd_1184_ = v_snd_1200_;
goto v___jp_1182_;
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_del_object(v___x_1163_);
lean_dec(v_snd_1161_);
lean_dec(v_fst_1160_);
lean_del_object(v___x_1158_);
lean_dec_ref(v_bodyUses_1147_);
v_a_1201_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1196_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1196_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
v___jp_1165_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1169_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___y_1168_, v_fvarId_1144_);
v___x_1170_ = lean_box(0);
v___x_1171_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_1172_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v___y_1167_);
v___x_1173_ = l_Lean_KVMap_setNat(v___x_1170_, v___x_1171_, v___x_1172_);
v___x_1174_ = l_Lean_Elab_Tactic_Do_addMData(v___x_1173_, v_fst_1160_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v___x_1169_);
lean_ctor_set(v___x_1163_, 0, v___y_1166_);
v___x_1176_ = v___x_1163_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___y_1166_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1169_);
v___x_1176_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1174_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 0, v___x_1177_);
v___x_1179_ = v___x_1158_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
v___jp_1182_:
{
uint8_t v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; uint8_t v___x_1189_; 
v___x_1185_ = 0;
v___x_1186_ = lean_box(v___x_1185_);
v___x_1187_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_bodyUses_1147_, v_fvarId_1144_, v___x_1186_);
lean_dec(v___x_1186_);
v___x_1188_ = lean_unbox(v___x_1187_);
v___x_1189_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v___x_1188_, v___x_1185_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1190_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_bodyUses_1147_, v_snd_1161_);
lean_dec_ref(v_bodyUses_1147_);
v___x_1191_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v___x_1190_, v_snd_1184_);
lean_dec_ref(v___x_1190_);
v___x_1192_ = lean_unbox(v___x_1187_);
lean_dec(v___x_1187_);
v___y_1166_ = v_fst_1183_;
v___y_1167_ = v___x_1192_;
v___y_1168_ = v___x_1191_;
goto v___jp_1165_;
}
else
{
uint8_t v___x_1193_; 
lean_dec_ref(v_snd_1184_);
lean_dec(v_snd_1161_);
v___x_1193_ = lean_unbox(v___x_1187_);
lean_dec(v___x_1187_);
v___y_1166_ = v_fst_1183_;
v___y_1167_ = v___x_1193_;
v___y_1168_ = v_bodyUses_1147_;
goto v___jp_1165_;
}
}
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_dec_ref(v_subst_1148_);
lean_dec_ref(v_bodyUses_1147_);
lean_dec(v_val_x3f_1146_);
v_a_1211_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1155_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1155_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___boxed(lean_object* v_fvarId_1219_, lean_object* v_ty_1220_, lean_object* v_val_x3f_1221_, lean_object* v_bodyUses_1222_, lean_object* v_subst_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_fvarId_1219_, v_ty_1220_, v_val_x3f_1221_, v_bodyUses_1222_, v_subst_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_fvarId_1219_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___boxed(lean_object* v_e_1230_, lean_object* v_subst_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_Elab_Tactic_Do_countUses(v_e_1230_, v_subst_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(lean_object* v_00_u03b2_1238_, lean_object* v_m_1239_, lean_object* v_a_1240_, lean_object* v_fallback_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_1239_, v_a_1240_, v_fallback_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(lean_object* v_00_u03b2_1243_, lean_object* v_m_1244_, lean_object* v_a_1245_, lean_object* v_fallback_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(v_00_u03b2_1243_, v_m_1244_, v_a_1245_, v_fallback_1246_);
lean_dec(v_fallback_1246_);
lean_dec(v_a_1245_);
lean_dec_ref(v_m_1244_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(lean_object* v_00_u03b2_1248_, lean_object* v_m_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_1249_, v_a_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(lean_object* v_00_u03b2_1252_, lean_object* v_m_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(v_00_u03b2_1252_, v_m_1253_, v_a_1254_);
lean_dec(v_a_1254_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(lean_object* v_00_u03b1_1256_, lean_object* v_msg_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___boxed(lean_object* v_00_u03b1_1264_, lean_object* v_msg_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(v_00_u03b1_1264_, v_msg_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4(lean_object* v_00_u03b2_1272_, lean_object* v_m_1273_, lean_object* v_a_1274_, lean_object* v_b_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v_m_1273_, v_a_1274_, v_b_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___boxed(lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(lean_object* v_00_u03b2_1289_, lean_object* v_a_1290_, lean_object* v_fallback_1291_, lean_object* v_x_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_1290_, v_fallback_1291_, v_x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1294_, lean_object* v_a_1295_, lean_object* v_fallback_1296_, lean_object* v_x_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(v_00_u03b2_1294_, v_a_1295_, v_fallback_1296_, v_x_1297_);
lean_dec(v_x_1297_);
lean_dec(v_fallback_1296_);
lean_dec(v_a_1295_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(lean_object* v_00_u03b2_1299_, lean_object* v_a_1300_, lean_object* v_x_1301_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_1300_, v_x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1303_, lean_object* v_a_1304_, lean_object* v_x_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(v_00_u03b2_1303_, v_a_1304_, v_x_1305_);
lean_dec(v_a_1304_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(lean_object* v_00_u03b2_1307_, lean_object* v_a_1308_, lean_object* v_b_1309_, lean_object* v_x_1310_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_1308_, v_b_1309_, v_x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(lean_object* v_as_1314_, size_t v_i_1315_, size_t v_stop_1316_, lean_object* v_b_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = lean_usize_dec_eq(v_i_1315_, v_stop_1316_);
if (v___x_1323_ == 0)
{
size_t v___x_1324_; size_t v___x_1325_; lean_object* v___x_1326_; 
v___x_1324_ = ((size_t)1ULL);
v___x_1325_ = lean_usize_sub(v_i_1315_, v___x_1324_);
v___x_1326_ = lean_array_uget_borrowed(v_as_1314_, v___x_1325_);
if (lean_obj_tag(v___x_1326_) == 0)
{
v_i_1315_ = v___x_1325_;
goto _start;
}
else
{
lean_object* v_val_1328_; lean_object* v_fst_1329_; lean_object* v_snd_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v_val_1328_ = lean_ctor_get(v___x_1326_, 0);
v_fst_1329_ = lean_ctor_get(v_b_1317_, 0);
lean_inc(v_fst_1329_);
v_snd_1330_ = lean_ctor_get(v_b_1317_, 1);
lean_inc(v_snd_1330_);
lean_dec_ref(v_b_1317_);
v___x_1331_ = l_Lean_LocalDecl_fvarId(v_val_1328_);
v___x_1332_ = l_Lean_LocalDecl_type(v_val_1328_);
v___x_1333_ = l_Lean_LocalDecl_value_x3f(v_val_1328_, v___x_1323_);
v___x_1334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_1335_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v___x_1331_, v___x_1332_, v___x_1333_, v_snd_1330_, v___x_1334_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___x_1331_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v_snd_1337_; lean_object* v_fst_1338_; lean_object* v_fst_1339_; lean_object* v_snd_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1355_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
v_snd_1337_ = lean_ctor_get(v_a_1336_, 1);
lean_inc(v_snd_1337_);
v_fst_1338_ = lean_ctor_get(v_a_1336_, 0);
lean_inc(v_fst_1338_);
lean_dec(v_a_1336_);
v_fst_1339_ = lean_ctor_get(v_snd_1337_, 0);
v_snd_1340_ = lean_ctor_get(v_snd_1337_, 1);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_snd_1337_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1342_ = v_snd_1337_;
v_isShared_1343_ = v_isSharedCheck_1355_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_snd_1340_);
lean_inc(v_fst_1339_);
lean_dec(v_snd_1337_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1355_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___y_1345_; 
if (lean_obj_tag(v_fst_1339_) == 0)
{
lean_object* v___x_1351_; 
lean_inc(v_val_1328_);
v___x_1351_ = l_Lean_LocalDecl_setType(v_val_1328_, v_fst_1338_);
v___y_1345_ = v___x_1351_;
goto v___jp_1344_;
}
else
{
lean_object* v_val_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_val_1352_ = lean_ctor_get(v_fst_1339_, 0);
lean_inc(v_val_1352_);
lean_dec_ref_known(v_fst_1339_, 1);
lean_inc(v_val_1328_);
v___x_1353_ = l_Lean_LocalDecl_setType(v_val_1328_, v_fst_1338_);
v___x_1354_ = l_Lean_LocalDecl_setValue(v___x_1353_, v_val_1352_);
v___y_1345_ = v___x_1354_;
goto v___jp_1344_;
}
v___jp_1344_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = lean_array_push(v_fst_1329_, v___y_1345_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1346_);
v___x_1348_ = v___x_1342_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_snd_1340_);
v___x_1348_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
v_i_1315_ = v___x_1325_;
v_b_1317_ = v___x_1348_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec(v_fst_1329_);
v_a_1356_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1335_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1335_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
else
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v_b_1317_);
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1365_, lean_object* v_i_1366_, lean_object* v_stop_1367_, lean_object* v_b_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
size_t v_i_boxed_1374_; size_t v_stop_boxed_1375_; lean_object* v_res_1376_; 
v_i_boxed_1374_ = lean_unbox_usize(v_i_1366_);
lean_dec(v_i_1366_);
v_stop_boxed_1375_ = lean_unbox_usize(v_stop_1367_);
lean_dec(v_stop_1367_);
v_res_1376_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_as_1365_, v_i_boxed_1374_, v_stop_boxed_1375_, v_b_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec_ref(v_as_1365_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(lean_object* v_x_1377_, lean_object* v_x_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
if (lean_obj_tag(v_x_1377_) == 0)
{
lean_object* v_cs_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1397_; 
v_cs_1384_ = lean_ctor_get(v_x_1377_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_x_1377_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1386_ = v_x_1377_;
v_isShared_1387_ = v_isSharedCheck_1397_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_cs_1384_);
lean_dec(v_x_1377_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1397_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1388_ = lean_array_get_size(v_cs_1384_);
v___x_1389_ = lean_unsigned_to_nat(0u);
v___x_1390_ = lean_nat_dec_lt(v___x_1389_, v___x_1388_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1392_; 
lean_dec_ref(v_cs_1384_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v_x_1378_);
v___x_1392_ = v___x_1386_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_x_1378_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
else
{
size_t v___x_1394_; size_t v___x_1395_; lean_object* v___x_1396_; 
lean_del_object(v___x_1386_);
v___x_1394_ = lean_usize_of_nat(v___x_1388_);
v___x_1395_ = ((size_t)0ULL);
v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_cs_1384_, v___x_1394_, v___x_1395_, v_x_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec_ref(v_cs_1384_);
return v___x_1396_;
}
}
}
else
{
lean_object* v_vs_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1411_; 
v_vs_1398_ = lean_ctor_get(v_x_1377_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_x_1377_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1400_ = v_x_1377_;
v_isShared_1401_ = v_isSharedCheck_1411_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_vs_1398_);
lean_dec(v_x_1377_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1411_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1402_ = lean_array_get_size(v_vs_1398_);
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1404_ = lean_nat_dec_lt(v___x_1403_, v___x_1402_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1406_; 
lean_dec_ref(v_vs_1398_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set_tag(v___x_1400_, 0);
lean_ctor_set(v___x_1400_, 0, v_x_1378_);
v___x_1406_ = v___x_1400_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_x_1378_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
else
{
size_t v___x_1408_; size_t v___x_1409_; lean_object* v___x_1410_; 
lean_del_object(v___x_1400_);
v___x_1408_ = lean_usize_of_nat(v___x_1402_);
v___x_1409_ = ((size_t)0ULL);
v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_vs_1398_, v___x_1408_, v___x_1409_, v_x_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec_ref(v_vs_1398_);
return v___x_1410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_1412_, size_t v_i_1413_, size_t v_stop_1414_, lean_object* v_b_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_usize_dec_eq(v_i_1413_, v_stop_1414_);
if (v___x_1421_ == 0)
{
size_t v___x_1422_; size_t v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1422_ = ((size_t)1ULL);
v___x_1423_ = lean_usize_sub(v_i_1413_, v___x_1422_);
v___x_1424_ = lean_array_uget_borrowed(v_as_1412_, v___x_1423_);
lean_inc(v___x_1424_);
v___x_1425_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v___x_1424_, v_b_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1425_, 1);
v_i_1413_ = v___x_1423_;
v_b_1415_ = v_a_1426_;
goto _start;
}
else
{
return v___x_1425_;
}
}
else
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v_b_1415_);
return v___x_1428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_1429_, lean_object* v_i_1430_, lean_object* v_stop_1431_, lean_object* v_b_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
size_t v_i_boxed_1438_; size_t v_stop_boxed_1439_; lean_object* v_res_1440_; 
v_i_boxed_1438_ = lean_unbox_usize(v_i_1430_);
lean_dec(v_i_1430_);
v_stop_boxed_1439_ = lean_unbox_usize(v_stop_1431_);
lean_dec(v_stop_1431_);
v_res_1440_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_as_1429_, v_i_boxed_1438_, v_stop_boxed_1439_, v_b_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec_ref(v_as_1429_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1441_, lean_object* v_x_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_x_1441_, v_x_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(lean_object* v_t_1449_, lean_object* v_init_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_root_1456_; lean_object* v_tail_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v_root_1456_ = lean_ctor_get(v_t_1449_, 0);
lean_inc_ref(v_root_1456_);
v_tail_1457_ = lean_ctor_get(v_t_1449_, 1);
lean_inc_ref(v_tail_1457_);
lean_dec_ref(v_t_1449_);
v___x_1458_ = lean_array_get_size(v_tail_1457_);
v___x_1459_ = lean_unsigned_to_nat(0u);
v___x_1460_ = lean_nat_dec_lt(v___x_1459_, v___x_1458_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; 
lean_dec_ref(v_tail_1457_);
v___x_1461_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1456_, v_init_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
return v___x_1461_;
}
else
{
size_t v___x_1462_; size_t v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = lean_usize_of_nat(v___x_1458_);
v___x_1463_ = ((size_t)0ULL);
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_tail_1457_, v___x_1462_, v___x_1463_, v_init_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec_ref(v_tail_1457_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1466_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1465_);
lean_dec_ref_known(v___x_1464_, 1);
v___x_1466_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1456_, v_a_1465_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
return v___x_1466_;
}
else
{
lean_dec_ref(v_root_1456_);
return v___x_1464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(lean_object* v_t_1467_, lean_object* v_init_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_t_1467_, v_init_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(lean_object* v_lctx_1475_, lean_object* v_init_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_decls_1482_; lean_object* v___x_1483_; 
v_decls_1482_ = lean_ctor_get(v_lctx_1475_, 1);
lean_inc_ref(v_decls_1482_);
lean_dec_ref(v_lctx_1475_);
v___x_1483_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_decls_1482_, v_init_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(lean_object* v_lctx_1484_, lean_object* v_init_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_lctx_1484_, v_init_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(size_t v_sz_1492_, size_t v_i_1493_, lean_object* v_bs_1494_, lean_object* v___y_1495_){
_start:
{
uint8_t v___x_1497_; 
v___x_1497_ = lean_usize_dec_lt(v_i_1493_, v_sz_1492_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v_bs_1494_);
return v___x_1498_;
}
else
{
lean_object* v_v_1499_; lean_object* v___x_1500_; lean_object* v_bs_x27_1501_; lean_object* v_a_1503_; 
v_v_1499_ = lean_array_uget(v_bs_1494_, v_i_1493_);
v___x_1500_ = lean_unsigned_to_nat(0u);
v_bs_x27_1501_ = lean_array_uset(v_bs_1494_, v_i_1493_, v___x_1500_);
if (lean_obj_tag(v_v_1499_) == 0)
{
v_a_1503_ = v_v_1499_;
goto v___jp_1502_;
}
else
{
lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1522_; 
v_isSharedCheck_1522_ = !lean_is_exclusive(v_v_1499_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; 
v_unused_1523_ = lean_ctor_get(v_v_1499_, 0);
lean_dec(v_unused_1523_);
v___x_1509_ = v_v_1499_;
v_isShared_1510_ = v_isSharedCheck_1522_;
goto v_resetjp_1508_;
}
else
{
lean_dec(v_v_1499_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1522_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1511_ = l_Lean_instInhabitedLocalDecl_default;
v___x_1512_ = lean_st_ref_take(v___y_1495_);
v___x_1513_ = lean_array_get_size(v___x_1512_);
v___x_1514_ = lean_unsigned_to_nat(1u);
v___x_1515_ = lean_nat_sub(v___x_1513_, v___x_1514_);
v___x_1516_ = lean_array_get(v___x_1511_, v___x_1512_, v___x_1515_);
lean_dec(v___x_1515_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1516_);
v___x_1518_ = v___x_1509_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = lean_array_pop(v___x_1512_);
v___x_1520_ = lean_st_ref_put(v___y_1495_, v___x_1519_);
v_a_1503_ = v___x_1518_;
goto v___jp_1502_;
}
}
}
v___jp_1502_:
{
size_t v___x_1504_; size_t v___x_1505_; lean_object* v___x_1506_; 
v___x_1504_ = ((size_t)1ULL);
v___x_1505_ = lean_usize_add(v_i_1493_, v___x_1504_);
v___x_1506_ = lean_array_uset(v_bs_x27_1501_, v_i_1493_, v_a_1503_);
v_i_1493_ = v___x_1505_;
v_bs_1494_ = v___x_1506_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg___boxed(lean_object* v_sz_1524_, lean_object* v_i_1525_, lean_object* v_bs_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
size_t v_sz_boxed_1529_; size_t v_i_boxed_1530_; lean_object* v_res_1531_; 
v_sz_boxed_1529_ = lean_unbox_usize(v_sz_1524_);
lean_dec(v_sz_1524_);
v_i_boxed_1530_ = lean_unbox_usize(v_i_1525_);
lean_dec(v_i_1525_);
v_res_1531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_boxed_1529_, v_i_boxed_1530_, v_bs_1526_, v___y_1527_);
lean_dec(v___y_1527_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(lean_object* v_x_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
if (lean_obj_tag(v_x_1532_) == 0)
{
lean_object* v_cs_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1565_; 
v_cs_1539_ = lean_ctor_get(v_x_1532_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_x_1532_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1541_ = v_x_1532_;
v_isShared_1542_ = v_isSharedCheck_1565_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_cs_1539_);
lean_dec(v_x_1532_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1565_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
size_t v_sz_1543_; size_t v___x_1544_; lean_object* v___x_1545_; 
v_sz_1543_ = lean_array_size(v_cs_1539_);
v___x_1544_ = ((size_t)0ULL);
v___x_1545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_1543_, v___x_1544_, v_cs_1539_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1556_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1556_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1556_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v_a_1546_);
v___x_1551_ = v___x_1541_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1553_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1551_);
v___x_1553_ = v___x_1548_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_del_object(v___x_1541_);
v_a_1557_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1545_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1545_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
else
{
lean_object* v_vs_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1592_; 
v_vs_1566_ = lean_ctor_get(v_x_1532_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_x_1532_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1568_ = v_x_1532_;
v_isShared_1569_ = v_isSharedCheck_1592_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_vs_1566_);
lean_dec(v_x_1532_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1592_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
size_t v_sz_1570_; size_t v___x_1571_; lean_object* v___x_1572_; 
v_sz_1570_ = lean_array_size(v_vs_1566_);
v___x_1571_ = ((size_t)0ULL);
v___x_1572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1570_, v___x_1571_, v_vs_1566_, v___y_1533_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1583_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1575_ = v___x_1572_;
v_isShared_1576_ = v_isSharedCheck_1583_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1572_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1583_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v_a_1573_);
v___x_1578_ = v___x_1568_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1580_; 
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1578_);
v___x_1580_ = v___x_1575_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_del_object(v___x_1568_);
v_a_1584_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1572_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1572_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(size_t v_sz_1593_, size_t v_i_1594_, lean_object* v_bs_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
uint8_t v___x_1602_; 
v___x_1602_ = lean_usize_dec_lt(v_i_1594_, v_sz_1593_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v_bs_1595_);
return v___x_1603_;
}
else
{
lean_object* v_v_1604_; lean_object* v___x_1605_; lean_object* v_bs_x27_1606_; lean_object* v___x_1607_; 
v_v_1604_ = lean_array_uget(v_bs_1595_, v_i_1594_);
v___x_1605_ = lean_unsigned_to_nat(0u);
v_bs_x27_1606_ = lean_array_uset(v_bs_1595_, v_i_1594_, v___x_1605_);
v___x_1607_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_v_1604_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; size_t v___x_1609_; size_t v___x_1610_; lean_object* v___x_1611_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 1);
v___x_1609_ = ((size_t)1ULL);
v___x_1610_ = lean_usize_add(v_i_1594_, v___x_1609_);
v___x_1611_ = lean_array_uset(v_bs_x27_1606_, v_i_1594_, v_a_1608_);
v_i_1594_ = v___x_1610_;
v_bs_1595_ = v___x_1611_;
goto _start;
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec_ref(v_bs_x27_1606_);
v_a_1613_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1607_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1607_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_sz_1621_, lean_object* v_i_1622_, lean_object* v_bs_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
size_t v_sz_boxed_1630_; size_t v_i_boxed_1631_; lean_object* v_res_1632_; 
v_sz_boxed_1630_ = lean_unbox_usize(v_sz_1621_);
lean_dec(v_sz_1621_);
v_i_boxed_1631_ = lean_unbox_usize(v_i_1622_);
lean_dec(v_i_1622_);
v_res_1632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_boxed_1630_, v_i_boxed_1631_, v_bs_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(lean_object* v_x_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_x_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(lean_object* v_t_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_root_1648_; lean_object* v_tail_1649_; lean_object* v_size_1650_; size_t v_shift_1651_; lean_object* v_tailOff_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1688_; 
v_root_1648_ = lean_ctor_get(v_t_1641_, 0);
v_tail_1649_ = lean_ctor_get(v_t_1641_, 1);
v_size_1650_ = lean_ctor_get(v_t_1641_, 2);
v_shift_1651_ = lean_ctor_get_usize(v_t_1641_, 4);
v_tailOff_1652_ = lean_ctor_get(v_t_1641_, 3);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_t_1641_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1654_ = v_t_1641_;
v_isShared_1655_ = v_isSharedCheck_1688_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_tailOff_1652_);
lean_inc(v_size_1650_);
lean_inc(v_tail_1649_);
lean_inc(v_root_1648_);
lean_dec(v_t_1641_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1688_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_root_1648_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; size_t v_sz_1658_; size_t v___x_1659_; lean_object* v___x_1660_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v_sz_1658_ = lean_array_size(v_tail_1649_);
v___x_1659_ = ((size_t)0ULL);
v___x_1660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1658_, v___x_1659_, v_tail_1649_, v___y_1642_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1671_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1671_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1671_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 1, v_a_1661_);
lean_ctor_set(v___x_1654_, 0, v_a_1657_);
v___x_1666_ = v___x_1654_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1657_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_a_1661_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v_size_1650_);
lean_ctor_set(v_reuseFailAlloc_1670_, 3, v_tailOff_1652_);
lean_ctor_set_usize(v_reuseFailAlloc_1670_, 4, v_shift_1651_);
v___x_1666_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1668_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1666_);
v___x_1668_ = v___x_1663_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v_a_1657_);
lean_del_object(v___x_1654_);
lean_dec(v_tailOff_1652_);
lean_dec(v_size_1650_);
v_a_1672_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1660_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1660_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_del_object(v___x_1654_);
lean_dec(v_tailOff_1652_);
lean_dec(v_size_1650_);
lean_dec_ref(v_tail_1649_);
v_a_1680_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1656_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1656_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1___boxed(lean_object* v_t_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_t_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx(lean_object* v_ctx_1697_, lean_object* v_targetUses_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_decls_1704_; lean_object* v_fvarIdToDecl_1705_; lean_object* v_auxDeclToFullName_1706_; lean_object* v_size_1707_; lean_object* v_decls_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v_decls_1704_ = lean_ctor_get(v_ctx_1697_, 1);
lean_inc_ref(v_decls_1704_);
v_fvarIdToDecl_1705_ = lean_ctor_get(v_ctx_1697_, 0);
lean_inc_ref(v_fvarIdToDecl_1705_);
v_auxDeclToFullName_1706_ = lean_ctor_get(v_ctx_1697_, 2);
lean_inc(v_auxDeclToFullName_1706_);
v_size_1707_ = lean_ctor_get(v_decls_1704_, 2);
v_decls_1708_ = lean_mk_empty_array_with_capacity(v_size_1707_);
v___x_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1709_, 0, v_decls_1708_);
lean_ctor_set(v___x_1709_, 1, v_targetUses_1698_);
v___x_1710_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_ctx_1697_, v___x_1709_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v_fst_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1710_, 1);
v_fst_1712_ = lean_ctor_get(v_a_1711_, 0);
lean_inc(v_fst_1712_);
lean_dec(v_a_1711_);
v___x_1713_ = lean_st_mk_ref(v_fst_1712_);
v___x_1714_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_decls_1704_, v___x_1713_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1724_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1724_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1724_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1719_ = lean_st_ref_get(v___x_1713_);
lean_dec(v___x_1713_);
lean_dec(v___x_1719_);
v___x_1720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1720_, 0, v_fvarIdToDecl_1705_);
lean_ctor_set(v___x_1720_, 1, v_a_1715_);
lean_ctor_set(v___x_1720_, 2, v_auxDeclToFullName_1706_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1720_);
v___x_1722_ = v___x_1717_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec(v___x_1713_);
lean_dec(v_auxDeclToFullName_1706_);
lean_dec_ref(v_fvarIdToDecl_1705_);
v_a_1725_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1714_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1714_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v_auxDeclToFullName_1706_);
lean_dec_ref(v_fvarIdToDecl_1705_);
lean_dec_ref(v_decls_1704_);
v_a_1733_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1710_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1710_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx___boxed(lean_object* v_ctx_1741_, lean_object* v_targetUses_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_ctx_1741_, v_targetUses_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(size_t v_sz_1749_, size_t v_i_1750_, lean_object* v_bs_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1749_, v_i_1750_, v_bs_1751_, v___y_1752_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(lean_object* v_sz_1759_, lean_object* v_i_1760_, lean_object* v_bs_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
size_t v_sz_boxed_1768_; size_t v_i_boxed_1769_; lean_object* v_res_1770_; 
v_sz_boxed_1768_ = lean_unbox_usize(v_sz_1759_);
lean_dec(v_sz_1759_);
v_i_boxed_1769_ = lean_unbox_usize(v_i_1760_);
lean_dec(v_i_1760_);
v_res_1770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(v_sz_boxed_1768_, v_i_boxed_1769_, v_bs_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
return v_res_1770_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_doNotDup(uint8_t v_u_1771_, lean_object* v_rhs_1772_, uint8_t v_elimTrivial_1773_){
_start:
{
uint8_t v___x_1774_; uint8_t v___x_1775_; 
v___x_1774_ = 2;
v___x_1775_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_u_1771_, v___x_1774_);
if (v___x_1775_ == 0)
{
return v___x_1775_;
}
else
{
if (v_elimTrivial_1773_ == 0)
{
return v___x_1775_;
}
else
{
uint8_t v___x_1776_; 
v___x_1776_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_rhs_1772_);
if (v___x_1776_ == 0)
{
return v___x_1775_;
}
else
{
uint8_t v___x_1777_; 
v___x_1777_ = 0;
return v___x_1777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_doNotDup___boxed(lean_object* v_u_1778_, lean_object* v_rhs_1779_, lean_object* v_elimTrivial_1780_){
_start:
{
uint8_t v_u_boxed_1781_; uint8_t v_elimTrivial_boxed_1782_; uint8_t v_res_1783_; lean_object* v_r_1784_; 
v_u_boxed_1781_ = lean_unbox(v_u_1778_);
v_elimTrivial_boxed_1782_ = lean_unbox(v_elimTrivial_1780_);
v_res_1783_ = l_Lean_Elab_Tactic_Do_doNotDup(v_u_boxed_1781_, v_rhs_1779_, v_elimTrivial_boxed_1782_);
lean_dec_ref(v_rhs_1779_);
v_r_1784_ = lean_box(v_res_1783_);
return v_r_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(uint8_t v_elimTrivial_1787_, lean_object* v_e_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
if (lean_obj_tag(v_e_1788_) == 8)
{
lean_object* v_type_1795_; 
v_type_1795_ = lean_ctor_get(v_e_1788_, 1);
if (lean_obj_tag(v_type_1795_) == 10)
{
lean_object* v_value_1796_; lean_object* v_body_1797_; lean_object* v_data_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; uint8_t v_uses_1802_; uint8_t v___x_1803_; 
v_value_1796_ = lean_ctor_get(v_e_1788_, 2);
v_body_1797_ = lean_ctor_get(v_e_1788_, 3);
v_data_1798_ = lean_ctor_get(v_type_1795_, 0);
v___x_1799_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_1800_ = lean_unsigned_to_nat(2u);
v___x_1801_ = l_Lean_KVMap_getNat(v_data_1798_, v___x_1799_, v___x_1800_);
v_uses_1802_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_1801_);
lean_dec(v___x_1801_);
v___x_1803_ = l_Lean_Elab_Tactic_Do_doNotDup(v_uses_1802_, v_value_1796_, v_elimTrivial_1787_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_expr_instantiate1(v_body_1797_, v_value_1796_);
v___x_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
return v___x_1808_;
}
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
return v___x_1810_;
}
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
return v___x_1812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(lean_object* v_elimTrivial_1813_, lean_object* v_e_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
uint8_t v_elimTrivial_boxed_1821_; lean_object* v_res_1822_; 
v_elimTrivial_boxed_1821_ = lean_unbox(v_elimTrivial_1813_);
v_res_1822_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(v_elimTrivial_boxed_1821_, v_e_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v_e_1814_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(lean_object* v_e_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1830_, 0, v_e_1823_);
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(lean_object* v_e_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(v_e_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
return v_res_1839_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = l_Lean_maxRecDepthErrorMessage;
v___x_1846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_1848_ = l_Lean_MessageData_ofFormat(v___x_1847_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_1850_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_1851_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v___x_1849_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_1852_){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v_ref_1852_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1857_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(lean_object* v_x_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v___y_1869_; lean_object* v_toCold_1878_; lean_object* v_currRecDepth_1879_; lean_object* v_ref_1880_; uint8_t v_diag_1881_; uint8_t v_suppressElabErrors_1882_; lean_object* v_maxRecDepth_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v_toCold_1878_ = lean_ctor_get(v___y_1865_, 0);
v_currRecDepth_1879_ = lean_ctor_get(v___y_1865_, 1);
v_ref_1880_ = lean_ctor_get(v___y_1865_, 2);
v_diag_1881_ = lean_ctor_get_uint8(v___y_1865_, sizeof(void*)*3);
v_suppressElabErrors_1882_ = lean_ctor_get_uint8(v___y_1865_, sizeof(void*)*3 + 1);
v_maxRecDepth_1888_ = lean_ctor_get(v_toCold_1878_, 3);
v___x_1889_ = lean_unsigned_to_nat(0u);
v___x_1890_ = lean_nat_dec_eq(v_maxRecDepth_1888_, v___x_1889_);
if (v___x_1890_ == 0)
{
uint8_t v___x_1891_; 
v___x_1891_ = lean_nat_dec_eq(v_currRecDepth_1879_, v_maxRecDepth_1888_);
if (v___x_1891_ == 0)
{
goto v___jp_1883_;
}
else
{
lean_object* v___x_1892_; 
lean_dec_ref(v_x_1860_);
lean_inc(v_ref_1880_);
v___x_1892_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1880_);
v___y_1869_ = v___x_1892_;
goto v___jp_1868_;
}
}
else
{
goto v___jp_1883_;
}
v___jp_1868_:
{
if (lean_obj_tag(v___y_1869_) == 0)
{
return v___y_1869_;
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
v_a_1870_ = lean_ctor_get(v___y_1869_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___y_1869_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___y_1869_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___y_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
v___jp_1883_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1884_ = lean_unsigned_to_nat(1u);
v___x_1885_ = lean_nat_add(v_currRecDepth_1879_, v___x_1884_);
lean_inc(v_ref_1880_);
lean_inc_ref(v_toCold_1878_);
v___x_1886_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1886_, 0, v_toCold_1878_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
lean_ctor_set(v___x_1886_, 2, v_ref_1880_);
lean_ctor_set_uint8(v___x_1886_, sizeof(void*)*3, v_diag_1881_);
lean_ctor_set_uint8(v___x_1886_, sizeof(void*)*3 + 1, v_suppressElabErrors_1882_);
lean_inc(v___y_1866_);
lean_inc(v___y_1864_);
lean_inc_ref(v___y_1863_);
lean_inc(v___y_1862_);
lean_inc(v___y_1861_);
v___x_1887_ = lean_apply_7(v_x_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___x_1886_, v___y_1866_, lean_box(0));
v___y_1869_ = v___x_1887_;
goto v___jp_1868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec(v___y_1894_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_1902_, lean_object* v_x_1903_){
_start:
{
if (lean_obj_tag(v_x_1903_) == 0)
{
lean_object* v___x_1904_; 
v___x_1904_ = lean_box(0);
return v___x_1904_;
}
else
{
lean_object* v_key_1905_; lean_object* v_value_1906_; lean_object* v_tail_1907_; uint8_t v___x_1908_; 
v_key_1905_ = lean_ctor_get(v_x_1903_, 0);
v_value_1906_ = lean_ctor_get(v_x_1903_, 1);
v_tail_1907_ = lean_ctor_get(v_x_1903_, 2);
v___x_1908_ = l_Lean_ExprStructEq_beq(v_key_1905_, v_a_1902_);
if (v___x_1908_ == 0)
{
v_x_1903_ = v_tail_1907_;
goto _start;
}
else
{
lean_object* v___x_1910_; 
lean_inc(v_value_1906_);
v___x_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1910_, 0, v_value_1906_);
return v___x_1910_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_1911_, lean_object* v_x_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1911_, v_x_1912_);
lean_dec(v_x_1912_);
lean_dec_ref(v_a_1911_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object* v_m_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v_buckets_1916_; lean_object* v___x_1917_; uint64_t v___x_1918_; uint64_t v___x_1919_; uint64_t v___x_1920_; uint64_t v_fold_1921_; uint64_t v___x_1922_; uint64_t v___x_1923_; uint64_t v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; size_t v___x_1927_; size_t v___x_1928_; size_t v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v_buckets_1916_ = lean_ctor_get(v_m_1914_, 1);
v___x_1917_ = lean_array_get_size(v_buckets_1916_);
v___x_1918_ = l_Lean_ExprStructEq_hash(v_a_1915_);
v___x_1919_ = 32ULL;
v___x_1920_ = lean_uint64_shift_right(v___x_1918_, v___x_1919_);
v_fold_1921_ = lean_uint64_xor(v___x_1918_, v___x_1920_);
v___x_1922_ = 16ULL;
v___x_1923_ = lean_uint64_shift_right(v_fold_1921_, v___x_1922_);
v___x_1924_ = lean_uint64_xor(v_fold_1921_, v___x_1923_);
v___x_1925_ = lean_uint64_to_usize(v___x_1924_);
v___x_1926_ = lean_usize_of_nat(v___x_1917_);
v___x_1927_ = ((size_t)1ULL);
v___x_1928_ = lean_usize_sub(v___x_1926_, v___x_1927_);
v___x_1929_ = lean_usize_land(v___x_1925_, v___x_1928_);
v___x_1930_ = lean_array_uget_borrowed(v_buckets_1916_, v___x_1929_);
v___x_1931_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1915_, v___x_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_1932_, v_a_1933_);
lean_dec_ref(v_a_1933_);
lean_dec_ref(v_m_1932_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v_b_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; 
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1940_);
lean_inc_ref(v___y_1939_);
lean_inc(v___y_1937_);
lean_inc(v___y_1936_);
v___x_1944_ = lean_apply_8(v_k_1935_, v_b_1938_, v___y_1936_, v___y_1937_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, lean_box(0));
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v_b_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_1945_, v___y_1946_, v___y_1947_, v_b_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1947_);
lean_dec(v___y_1946_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_1955_, lean_object* v_type_1956_, lean_object* v_val_1957_, lean_object* v_k_1958_, uint8_t v_nondep_1959_, uint8_t v_kind_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v___f_1968_; lean_object* v___x_1969_; 
lean_inc(v___y_1962_);
lean_inc(v___y_1961_);
v___f_1968_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1968_, 0, v_k_1958_);
lean_closure_set(v___f_1968_, 1, v___y_1961_);
lean_closure_set(v___f_1968_, 2, v___y_1962_);
v___x_1969_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1955_, v_type_1956_, v_val_1957_, v___f_1968_, v_nondep_1959_, v_kind_1960_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
if (lean_obj_tag(v___x_1969_) == 0)
{
return v___x_1969_;
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_1978_, lean_object* v_type_1979_, lean_object* v_val_1980_, lean_object* v_k_1981_, lean_object* v_nondep_1982_, lean_object* v_kind_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
uint8_t v_nondep_boxed_1991_; uint8_t v_kind_boxed_1992_; lean_object* v_res_1993_; 
v_nondep_boxed_1991_ = lean_unbox(v_nondep_1982_);
v_kind_boxed_1992_ = lean_unbox(v_kind_1983_);
v_res_1993_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1978_, v_type_1979_, v_val_1980_, v_k_1981_, v_nondep_boxed_1991_, v_kind_boxed_1992_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec(v___y_1984_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_1994_, uint8_t v_bi_1995_, lean_object* v_type_1996_, lean_object* v_k_1997_, uint8_t v_kind_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v___f_2006_; lean_object* v___x_2007_; 
lean_inc(v___y_2000_);
lean_inc(v___y_1999_);
v___f_2006_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2006_, 0, v_k_1997_);
lean_closure_set(v___f_2006_, 1, v___y_1999_);
lean_closure_set(v___f_2006_, 2, v___y_2000_);
v___x_2007_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1994_, v_bi_1995_, v_type_1996_, v___f_2006_, v_kind_1998_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
if (lean_obj_tag(v___x_2007_) == 0)
{
return v___x_2007_;
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_2016_, lean_object* v_bi_2017_, lean_object* v_type_2018_, lean_object* v_k_2019_, lean_object* v_kind_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
uint8_t v_bi_boxed_2028_; uint8_t v_kind_boxed_2029_; lean_object* v_res_2030_; 
v_bi_boxed_2028_ = lean_unbox(v_bi_2017_);
v_kind_boxed_2029_ = lean_unbox(v_kind_2020_);
v_res_2030_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_2016_, v_bi_boxed_2028_, v_type_2018_, v_k_2019_, v_kind_boxed_2029_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec(v___y_2021_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2031_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(v___x_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2047_, lean_object* v_x_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_apply_1(v_x_2048_, lean_box(0));
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2057_, lean_object* v_x_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(v_00_u03b1_2057_, v_x_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_2066_, lean_object* v_x_2067_){
_start:
{
if (lean_obj_tag(v_x_2067_) == 0)
{
return v_x_2066_;
}
else
{
lean_object* v_key_2068_; lean_object* v_value_2069_; lean_object* v_tail_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2093_; 
v_key_2068_ = lean_ctor_get(v_x_2067_, 0);
v_value_2069_ = lean_ctor_get(v_x_2067_, 1);
v_tail_2070_ = lean_ctor_get(v_x_2067_, 2);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_x_2067_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2072_ = v_x_2067_;
v_isShared_2073_ = v_isSharedCheck_2093_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_tail_2070_);
lean_inc(v_value_2069_);
lean_inc(v_key_2068_);
lean_dec(v_x_2067_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2093_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; uint64_t v___x_2075_; uint64_t v___x_2076_; uint64_t v___x_2077_; uint64_t v_fold_2078_; uint64_t v___x_2079_; uint64_t v___x_2080_; uint64_t v___x_2081_; size_t v___x_2082_; size_t v___x_2083_; size_t v___x_2084_; size_t v___x_2085_; size_t v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2074_ = lean_array_get_size(v_x_2066_);
v___x_2075_ = l_Lean_ExprStructEq_hash(v_key_2068_);
v___x_2076_ = 32ULL;
v___x_2077_ = lean_uint64_shift_right(v___x_2075_, v___x_2076_);
v_fold_2078_ = lean_uint64_xor(v___x_2075_, v___x_2077_);
v___x_2079_ = 16ULL;
v___x_2080_ = lean_uint64_shift_right(v_fold_2078_, v___x_2079_);
v___x_2081_ = lean_uint64_xor(v_fold_2078_, v___x_2080_);
v___x_2082_ = lean_uint64_to_usize(v___x_2081_);
v___x_2083_ = lean_usize_of_nat(v___x_2074_);
v___x_2084_ = ((size_t)1ULL);
v___x_2085_ = lean_usize_sub(v___x_2083_, v___x_2084_);
v___x_2086_ = lean_usize_land(v___x_2082_, v___x_2085_);
v___x_2087_ = lean_array_uget_borrowed(v_x_2066_, v___x_2086_);
lean_inc(v___x_2087_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 2, v___x_2087_);
v___x_2089_ = v___x_2072_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_key_2068_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_value_2069_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_array_uset(v_x_2066_, v___x_2086_, v___x_2089_);
v_x_2066_ = v___x_2090_;
v_x_2067_ = v_tail_2070_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_2094_, lean_object* v_source_2095_, lean_object* v_target_2096_){
_start:
{
lean_object* v___x_2097_; uint8_t v___x_2098_; 
v___x_2097_ = lean_array_get_size(v_source_2095_);
v___x_2098_ = lean_nat_dec_lt(v_i_2094_, v___x_2097_);
if (v___x_2098_ == 0)
{
lean_dec_ref(v_source_2095_);
lean_dec(v_i_2094_);
return v_target_2096_;
}
else
{
lean_object* v_es_2099_; lean_object* v___x_2100_; lean_object* v_source_2101_; lean_object* v_target_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v_es_2099_ = lean_array_fget(v_source_2095_, v_i_2094_);
v___x_2100_ = lean_box(0);
v_source_2101_ = lean_array_fset(v_source_2095_, v_i_2094_, v___x_2100_);
v_target_2102_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_2096_, v_es_2099_);
v___x_2103_ = lean_unsigned_to_nat(1u);
v___x_2104_ = lean_nat_add(v_i_2094_, v___x_2103_);
lean_dec(v_i_2094_);
v_i_2094_ = v___x_2104_;
v_source_2095_ = v_source_2101_;
v_target_2096_ = v_target_2102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_2106_){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v_nbuckets_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2107_ = lean_array_get_size(v_data_2106_);
v___x_2108_ = lean_unsigned_to_nat(2u);
v_nbuckets_2109_ = lean_nat_mul(v___x_2107_, v___x_2108_);
v___x_2110_ = lean_unsigned_to_nat(0u);
v___x_2111_ = lean_box(0);
v___x_2112_ = lean_mk_array(v_nbuckets_2109_, v___x_2111_);
v___x_2113_ = lean_array_propagate_mark(v_data_2106_, v___x_2112_);
v___x_2114_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_2110_, v_data_2106_, v___x_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_2115_, lean_object* v_b_2116_, lean_object* v_x_2117_){
_start:
{
if (lean_obj_tag(v_x_2117_) == 0)
{
lean_dec(v_b_2116_);
lean_dec_ref(v_a_2115_);
return v_x_2117_;
}
else
{
lean_object* v_key_2118_; lean_object* v_value_2119_; lean_object* v_tail_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2132_; 
v_key_2118_ = lean_ctor_get(v_x_2117_, 0);
v_value_2119_ = lean_ctor_get(v_x_2117_, 1);
v_tail_2120_ = lean_ctor_get(v_x_2117_, 2);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_x_2117_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2122_ = v_x_2117_;
v_isShared_2123_ = v_isSharedCheck_2132_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_tail_2120_);
lean_inc(v_value_2119_);
lean_inc(v_key_2118_);
lean_dec(v_x_2117_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2132_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
uint8_t v___x_2124_; 
v___x_2124_ = l_Lean_ExprStructEq_beq(v_key_2118_, v_a_2115_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
v___x_2125_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2115_, v_b_2116_, v_tail_2120_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 2, v___x_2125_);
v___x_2127_ = v___x_2122_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_key_2118_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_value_2119_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
else
{
lean_object* v___x_2130_; 
lean_dec(v_value_2119_);
lean_dec(v_key_2118_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 1, v_b_2116_);
lean_ctor_set(v___x_2122_, 0, v_a_2115_);
v___x_2130_ = v___x_2122_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2115_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_b_2116_);
lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_tail_2120_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_2133_, lean_object* v_x_2134_){
_start:
{
if (lean_obj_tag(v_x_2134_) == 0)
{
uint8_t v___x_2135_; 
v___x_2135_ = 0;
return v___x_2135_;
}
else
{
lean_object* v_key_2136_; lean_object* v_tail_2137_; uint8_t v___x_2138_; 
v_key_2136_ = lean_ctor_get(v_x_2134_, 0);
v_tail_2137_ = lean_ctor_get(v_x_2134_, 2);
v___x_2138_ = l_Lean_ExprStructEq_beq(v_key_2136_, v_a_2133_);
if (v___x_2138_ == 0)
{
v_x_2134_ = v_tail_2137_;
goto _start;
}
else
{
return v___x_2138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_2140_, lean_object* v_x_2141_){
_start:
{
uint8_t v_res_2142_; lean_object* v_r_2143_; 
v_res_2142_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2140_, v_x_2141_);
lean_dec(v_x_2141_);
lean_dec_ref(v_a_2140_);
v_r_2143_ = lean_box(v_res_2142_);
return v_r_2143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object* v_m_2144_, lean_object* v_a_2145_, lean_object* v_b_2146_){
_start:
{
lean_object* v_size_2147_; lean_object* v_buckets_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2191_; 
v_size_2147_ = lean_ctor_get(v_m_2144_, 0);
v_buckets_2148_ = lean_ctor_get(v_m_2144_, 1);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_m_2144_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2150_ = v_m_2144_;
v_isShared_2151_ = v_isSharedCheck_2191_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_buckets_2148_);
lean_inc(v_size_2147_);
lean_dec(v_m_2144_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2191_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; uint64_t v___x_2153_; uint64_t v___x_2154_; uint64_t v___x_2155_; uint64_t v_fold_2156_; uint64_t v___x_2157_; uint64_t v___x_2158_; uint64_t v___x_2159_; size_t v___x_2160_; size_t v___x_2161_; size_t v___x_2162_; size_t v___x_2163_; size_t v___x_2164_; lean_object* v_bkt_2165_; uint8_t v___x_2166_; 
v___x_2152_ = lean_array_get_size(v_buckets_2148_);
v___x_2153_ = l_Lean_ExprStructEq_hash(v_a_2145_);
v___x_2154_ = 32ULL;
v___x_2155_ = lean_uint64_shift_right(v___x_2153_, v___x_2154_);
v_fold_2156_ = lean_uint64_xor(v___x_2153_, v___x_2155_);
v___x_2157_ = 16ULL;
v___x_2158_ = lean_uint64_shift_right(v_fold_2156_, v___x_2157_);
v___x_2159_ = lean_uint64_xor(v_fold_2156_, v___x_2158_);
v___x_2160_ = lean_uint64_to_usize(v___x_2159_);
v___x_2161_ = lean_usize_of_nat(v___x_2152_);
v___x_2162_ = ((size_t)1ULL);
v___x_2163_ = lean_usize_sub(v___x_2161_, v___x_2162_);
v___x_2164_ = lean_usize_land(v___x_2160_, v___x_2163_);
v_bkt_2165_ = lean_array_uget_borrowed(v_buckets_2148_, v___x_2164_);
v___x_2166_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2145_, v_bkt_2165_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; lean_object* v_size_x27_2168_; lean_object* v___x_2169_; lean_object* v_buckets_x27_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2167_ = lean_unsigned_to_nat(1u);
v_size_x27_2168_ = lean_nat_add(v_size_2147_, v___x_2167_);
lean_dec(v_size_2147_);
lean_inc(v_bkt_2165_);
v___x_2169_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2169_, 0, v_a_2145_);
lean_ctor_set(v___x_2169_, 1, v_b_2146_);
lean_ctor_set(v___x_2169_, 2, v_bkt_2165_);
v_buckets_x27_2170_ = lean_array_uset(v_buckets_2148_, v___x_2164_, v___x_2169_);
v___x_2171_ = lean_unsigned_to_nat(4u);
v___x_2172_ = lean_nat_mul(v_size_x27_2168_, v___x_2171_);
v___x_2173_ = lean_unsigned_to_nat(3u);
v___x_2174_ = lean_nat_div(v___x_2172_, v___x_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_array_get_size(v_buckets_x27_2170_);
v___x_2176_ = lean_nat_dec_le(v___x_2174_, v___x_2175_);
lean_dec(v___x_2174_);
if (v___x_2176_ == 0)
{
lean_object* v_val_2177_; lean_object* v___x_2179_; 
v_val_2177_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_2170_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 1, v_val_2177_);
lean_ctor_set(v___x_2150_, 0, v_size_x27_2168_);
v___x_2179_ = v___x_2150_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_size_x27_2168_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_val_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
else
{
lean_object* v___x_2182_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 1, v_buckets_x27_2170_);
lean_ctor_set(v___x_2150_, 0, v_size_x27_2168_);
v___x_2182_ = v___x_2150_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_size_x27_2168_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_buckets_x27_2170_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
else
{
lean_object* v___x_2184_; lean_object* v_buckets_x27_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2189_; 
lean_inc(v_bkt_2165_);
v___x_2184_ = lean_box(0);
v_buckets_x27_2185_ = lean_array_uset(v_buckets_2148_, v___x_2164_, v___x_2184_);
v___x_2186_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2145_, v_b_2146_, v_bkt_2165_);
v___x_2187_ = lean_array_uset(v_buckets_x27_2185_, v___x_2164_, v___x_2186_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 1, v___x_2187_);
v___x_2189_ = v___x_2150_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_size_2147_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object* v_a_2192_, lean_object* v_e_2193_, lean_object* v_a_2194_){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2196_ = lean_st_ref_take(v_a_2192_);
v___x_2197_ = lean_box(0);
v___x_2198_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v___x_2196_, v_e_2193_, v_a_2194_);
v___x_2199_ = lean_st_ref_put(v_a_2192_, v___x_2198_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2200_, lean_object* v_e_2201_, lean_object* v_a_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(v_a_2200_, v_e_2201_, v_a_2202_);
lean_dec(v_a_2200_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_2205_, lean_object* v_pre_2206_, lean_object* v_post_2207_, lean_object* v_usedLetOnly_2208_, lean_object* v_skipConstInApp_2209_, lean_object* v_skipInstances_2210_, lean_object* v_body_2211_, lean_object* v_x_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
uint8_t v_usedLetOnly_boxed_2220_; uint8_t v_skipConstInApp_boxed_2221_; uint8_t v_skipInstances_boxed_2222_; lean_object* v_res_2223_; 
v_usedLetOnly_boxed_2220_ = lean_unbox(v_usedLetOnly_2208_);
v_skipConstInApp_boxed_2221_ = lean_unbox(v_skipConstInApp_2209_);
v_skipInstances_boxed_2222_ = lean_unbox(v_skipInstances_2210_);
v_res_2223_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(v_fvars_2205_, v_pre_2206_, v_post_2207_, v_usedLetOnly_boxed_2220_, v_skipConstInApp_boxed_2221_, v_skipInstances_boxed_2222_, v_body_2211_, v_x_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec(v___y_2213_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_2227_, lean_object* v_pre_2228_, lean_object* v_post_2229_, uint8_t v_usedLetOnly_2230_, uint8_t v_skipConstInApp_2231_, uint8_t v_skipInstances_2232_, lean_object* v_body_2233_, lean_object* v_x_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = lean_array_push(v_fvars_2227_, v_x_2234_);
v___x_2243_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2228_, v_post_2229_, v_usedLetOnly_2230_, v_skipConstInApp_2231_, v_skipInstances_2232_, v___x_2242_, v_body_2233_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_2244_, lean_object* v_pre_2245_, lean_object* v_post_2246_, lean_object* v_usedLetOnly_2247_, lean_object* v_skipConstInApp_2248_, lean_object* v_skipInstances_2249_, lean_object* v_body_2250_, lean_object* v_x_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
uint8_t v_usedLetOnly_boxed_2259_; uint8_t v_skipConstInApp_boxed_2260_; uint8_t v_skipInstances_boxed_2261_; lean_object* v_res_2262_; 
v_usedLetOnly_boxed_2259_ = lean_unbox(v_usedLetOnly_2247_);
v_skipConstInApp_boxed_2260_ = lean_unbox(v_skipConstInApp_2248_);
v_skipInstances_boxed_2261_ = lean_unbox(v_skipInstances_2249_);
v_res_2262_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(v_fvars_2244_, v_pre_2245_, v_post_2246_, v_usedLetOnly_boxed_2259_, v_skipConstInApp_boxed_2260_, v_skipInstances_boxed_2261_, v_body_2250_, v_x_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec(v___y_2252_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(lean_object* v_pre_2263_, lean_object* v_post_2264_, uint8_t v_usedLetOnly_2265_, uint8_t v_skipConstInApp_2266_, uint8_t v_skipInstances_2267_, lean_object* v_e_2268_, lean_object* v_a_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v___x_2276_; 
lean_inc_ref(v_post_2264_);
lean_inc(v___y_2274_);
lean_inc_ref(v___y_2273_);
lean_inc(v___y_2272_);
lean_inc_ref(v___y_2271_);
lean_inc(v___y_2270_);
lean_inc_ref(v_e_2268_);
v___x_2276_ = lean_apply_7(v_post_2264_, v_e_2268_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, lean_box(0));
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2295_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2295_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2295_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
switch(lean_obj_tag(v_a_2277_))
{
case 0:
{
lean_object* v_e_2281_; lean_object* v___x_2283_; 
lean_dec_ref(v_e_2268_);
lean_dec_ref(v_post_2264_);
lean_dec_ref(v_pre_2263_);
v_e_2281_ = lean_ctor_get(v_a_2277_, 0);
lean_inc_ref(v_e_2281_);
lean_dec_ref_known(v_a_2277_, 1);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v_e_2281_);
v___x_2283_ = v___x_2279_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_e_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
case 1:
{
lean_object* v_e_2285_; lean_object* v___x_2286_; 
lean_del_object(v___x_2279_);
lean_dec_ref(v_e_2268_);
v_e_2285_ = lean_ctor_get(v_a_2277_, 0);
lean_inc_ref(v_e_2285_);
lean_dec_ref_known(v_a_2277_, 1);
v___x_2286_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2263_, v_post_2264_, v_usedLetOnly_2265_, v_skipConstInApp_2266_, v_skipInstances_2267_, v_e_2285_, v_a_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
return v___x_2286_;
}
default: 
{
lean_object* v_e_x3f_2287_; 
lean_dec_ref(v_post_2264_);
lean_dec_ref(v_pre_2263_);
v_e_x3f_2287_ = lean_ctor_get(v_a_2277_, 0);
lean_inc(v_e_x3f_2287_);
lean_dec_ref_known(v_a_2277_, 1);
if (lean_obj_tag(v_e_x3f_2287_) == 0)
{
lean_object* v___x_2289_; 
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v_e_2268_);
v___x_2289_ = v___x_2279_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_e_2268_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
else
{
lean_object* v_val_2291_; lean_object* v___x_2293_; 
lean_dec_ref(v_e_2268_);
v_val_2291_ = lean_ctor_get(v_e_x3f_2287_, 0);
lean_inc(v_val_2291_);
lean_dec_ref_known(v_e_x3f_2287_, 1);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v_val_2291_);
v___x_2293_ = v___x_2279_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_val_2291_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec_ref(v_e_2268_);
lean_dec_ref(v_post_2264_);
lean_dec_ref(v_pre_2263_);
v_a_2296_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2276_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2276_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(lean_object* v_pre_2304_, lean_object* v_post_2305_, uint8_t v_usedLetOnly_2306_, uint8_t v_skipConstInApp_2307_, uint8_t v_skipInstances_2308_, lean_object* v_fvars_2309_, lean_object* v_e_2310_, lean_object* v_a_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
if (lean_obj_tag(v_e_2310_) == 6)
{
lean_object* v_binderName_2318_; lean_object* v_binderType_2319_; lean_object* v_body_2320_; uint8_t v_binderInfo_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___f_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v_binderName_2318_ = lean_ctor_get(v_e_2310_, 0);
lean_inc(v_binderName_2318_);
v_binderType_2319_ = lean_ctor_get(v_e_2310_, 1);
lean_inc_ref(v_binderType_2319_);
v_body_2320_ = lean_ctor_get(v_e_2310_, 2);
lean_inc_ref(v_body_2320_);
v_binderInfo_2321_ = lean_ctor_get_uint8(v_e_2310_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2310_, 3);
v___x_2322_ = lean_box(v_usedLetOnly_2306_);
v___x_2323_ = lean_box(v_skipConstInApp_2307_);
v___x_2324_ = lean_box(v_skipInstances_2308_);
lean_inc_ref(v_post_2305_);
lean_inc_ref(v_pre_2304_);
lean_inc_ref(v_fvars_2309_);
v___f_2325_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2325_, 0, v_fvars_2309_);
lean_closure_set(v___f_2325_, 1, v_pre_2304_);
lean_closure_set(v___f_2325_, 2, v_post_2305_);
lean_closure_set(v___f_2325_, 3, v___x_2322_);
lean_closure_set(v___f_2325_, 4, v___x_2323_);
lean_closure_set(v___f_2325_, 5, v___x_2324_);
lean_closure_set(v___f_2325_, 6, v_body_2320_);
v___x_2326_ = lean_expr_instantiate_rev(v_binderType_2319_, v_fvars_2309_);
lean_dec_ref(v_fvars_2309_);
lean_dec_ref(v_binderType_2319_);
v___x_2327_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2304_, v_post_2305_, v_usedLetOnly_2306_, v_skipConstInApp_2307_, v_skipInstances_2308_, v___x_2326_, v_a_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref_known(v___x_2327_, 1);
v___x_2329_ = 0;
v___x_2330_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2318_, v_binderInfo_2321_, v_a_2328_, v___f_2325_, v___x_2329_, v_a_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
return v___x_2330_;
}
else
{
lean_dec_ref(v___f_2325_);
lean_dec(v_binderName_2318_);
return v___x_2327_;
}
}
else
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = lean_expr_instantiate_rev(v_e_2310_, v_fvars_2309_);
lean_dec_ref(v_e_2310_);
lean_inc_ref(v_post_2305_);
lean_inc_ref(v_pre_2304_);
v___x_2332_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2304_, v_post_2305_, v_usedLetOnly_2306_, v_skipConstInApp_2307_, v_skipInstances_2308_, v___x_2331_, v_a_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; uint8_t v___x_2334_; uint8_t v___x_2335_; uint8_t v___x_2336_; lean_object* v___x_2337_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v___x_2334_ = 0;
v___x_2335_ = 1;
v___x_2336_ = 1;
v___x_2337_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2309_, v_a_2333_, v___x_2334_, v_usedLetOnly_2306_, v___x_2334_, v___x_2335_, v___x_2336_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec_ref(v_fvars_2309_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2304_, v_post_2305_, v_usedLetOnly_2306_, v_skipConstInApp_2307_, v_skipInstances_2308_, v_a_2338_, v_a_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
return v___x_2339_;
}
else
{
lean_dec_ref(v_post_2305_);
lean_dec_ref(v_pre_2304_);
return v___x_2337_;
}
}
else
{
lean_dec_ref(v_fvars_2309_);
lean_dec_ref(v_post_2305_);
lean_dec_ref(v_pre_2304_);
return v___x_2332_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_2340_, lean_object* v_pre_2341_, lean_object* v_post_2342_, uint8_t v_usedLetOnly_2343_, uint8_t v_skipConstInApp_2344_, uint8_t v_skipInstances_2345_, lean_object* v_body_2346_, lean_object* v_x_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = lean_array_push(v_fvars_2340_, v_x_2347_);
v___x_2356_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2341_, v_post_2342_, v_usedLetOnly_2343_, v_skipConstInApp_2344_, v_skipInstances_2345_, v___x_2355_, v_body_2346_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_2357_, lean_object* v_pre_2358_, lean_object* v_post_2359_, lean_object* v_usedLetOnly_2360_, lean_object* v_skipConstInApp_2361_, lean_object* v_skipInstances_2362_, lean_object* v_body_2363_, lean_object* v_x_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
uint8_t v_usedLetOnly_boxed_2372_; uint8_t v_skipConstInApp_boxed_2373_; uint8_t v_skipInstances_boxed_2374_; lean_object* v_res_2375_; 
v_usedLetOnly_boxed_2372_ = lean_unbox(v_usedLetOnly_2360_);
v_skipConstInApp_boxed_2373_ = lean_unbox(v_skipConstInApp_2361_);
v_skipInstances_boxed_2374_ = lean_unbox(v_skipInstances_2362_);
v_res_2375_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(v_fvars_2357_, v_pre_2358_, v_post_2359_, v_usedLetOnly_boxed_2372_, v_skipConstInApp_boxed_2373_, v_skipInstances_boxed_2374_, v_body_2363_, v_x_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec(v___y_2365_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(lean_object* v_pre_2376_, lean_object* v_post_2377_, uint8_t v_usedLetOnly_2378_, uint8_t v_skipConstInApp_2379_, uint8_t v_skipInstances_2380_, lean_object* v_fvars_2381_, lean_object* v_e_2382_, lean_object* v_a_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
if (lean_obj_tag(v_e_2382_) == 8)
{
lean_object* v_declName_2390_; lean_object* v_type_2391_; lean_object* v_value_2392_; lean_object* v_body_2393_; uint8_t v_nondep_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___f_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v_declName_2390_ = lean_ctor_get(v_e_2382_, 0);
lean_inc(v_declName_2390_);
v_type_2391_ = lean_ctor_get(v_e_2382_, 1);
lean_inc_ref(v_type_2391_);
v_value_2392_ = lean_ctor_get(v_e_2382_, 2);
lean_inc_ref(v_value_2392_);
v_body_2393_ = lean_ctor_get(v_e_2382_, 3);
lean_inc_ref(v_body_2393_);
v_nondep_2394_ = lean_ctor_get_uint8(v_e_2382_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2382_, 4);
v___x_2395_ = lean_box(v_usedLetOnly_2378_);
v___x_2396_ = lean_box(v_skipConstInApp_2379_);
v___x_2397_ = lean_box(v_skipInstances_2380_);
lean_inc_ref_n(v_post_2377_, 2);
lean_inc_ref_n(v_pre_2376_, 2);
lean_inc_ref(v_fvars_2381_);
v___f_2398_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2398_, 0, v_fvars_2381_);
lean_closure_set(v___f_2398_, 1, v_pre_2376_);
lean_closure_set(v___f_2398_, 2, v_post_2377_);
lean_closure_set(v___f_2398_, 3, v___x_2395_);
lean_closure_set(v___f_2398_, 4, v___x_2396_);
lean_closure_set(v___f_2398_, 5, v___x_2397_);
lean_closure_set(v___f_2398_, 6, v_body_2393_);
v___x_2399_ = lean_expr_instantiate_rev(v_type_2391_, v_fvars_2381_);
lean_dec_ref(v_type_2391_);
v___x_2400_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2376_, v_post_2377_, v_usedLetOnly_2378_, v_skipConstInApp_2379_, v_skipInstances_2380_, v___x_2399_, v_a_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2400_, 1);
v___x_2402_ = lean_expr_instantiate_rev(v_value_2392_, v_fvars_2381_);
lean_dec_ref(v_fvars_2381_);
lean_dec_ref(v_value_2392_);
v___x_2403_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2376_, v_post_2377_, v_usedLetOnly_2378_, v_skipConstInApp_2379_, v_skipInstances_2380_, v___x_2402_, v_a_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; uint8_t v___x_2405_; lean_object* v___x_2406_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___x_2403_, 1);
v___x_2405_ = 0;
v___x_2406_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_2390_, v_a_2401_, v_a_2404_, v___f_2398_, v_nondep_2394_, v___x_2405_, v_a_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
return v___x_2406_;
}
else
{
lean_dec(v_a_2401_);
lean_dec_ref(v___f_2398_);
lean_dec(v_declName_2390_);
return v___x_2403_;
}
}
else
{
lean_dec_ref(v___f_2398_);
lean_dec_ref(v_value_2392_);
lean_dec(v_declName_2390_);
lean_dec_ref(v_fvars_2381_);
lean_dec_ref(v_post_2377_);
lean_dec_ref(v_pre_2376_);
return v___x_2400_;
}
}
else
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_expr_instantiate_rev(v_e_2382_, v_fvars_2381_);
lean_dec_ref(v_e_2382_);
lean_inc_ref(v_post_2377_);
lean_inc_ref(v_pre_2376_);
v___x_2408_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2376_, v_post_2377_, v_usedLetOnly_2378_, v_skipConstInApp_2379_, v_skipInstances_2380_, v___x_2407_, v_a_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; uint8_t v___x_2410_; uint8_t v___x_2411_; lean_object* v___x_2412_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2408_, 1);
v___x_2410_ = 0;
v___x_2411_ = 1;
v___x_2412_ = l_Lean_Meta_mkLetFVars(v_fvars_2381_, v_a_2409_, v_usedLetOnly_2378_, v___x_2410_, v___x_2411_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec_ref(v_fvars_2381_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; lean_object* v___x_2414_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2412_, 1);
v___x_2414_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2376_, v_post_2377_, v_usedLetOnly_2378_, v_skipConstInApp_2379_, v_skipInstances_2380_, v_a_2413_, v_a_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
return v___x_2414_;
}
else
{
lean_dec_ref(v_post_2377_);
lean_dec_ref(v_pre_2376_);
return v___x_2412_;
}
}
else
{
lean_dec_ref(v_fvars_2381_);
lean_dec_ref(v_post_2377_);
lean_dec_ref(v_pre_2376_);
return v___x_2408_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2415_; lean_object* v_dummy_2416_; 
v___x_2415_ = lean_box(0);
v_dummy_2416_ = l_Lean_Expr_sort___override(v___x_2415_);
return v_dummy_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(lean_object* v_pre_2417_, lean_object* v_post_2418_, uint8_t v_usedLetOnly_2419_, uint8_t v_skipConstInApp_2420_, uint8_t v_skipInstances_2421_, size_t v_sz_2422_, size_t v_i_2423_, lean_object* v_bs_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
uint8_t v___x_2432_; 
v___x_2432_ = lean_usize_dec_lt(v_i_2423_, v_sz_2422_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; 
lean_dec_ref(v_post_2418_);
lean_dec_ref(v_pre_2417_);
v___x_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2433_, 0, v_bs_2424_);
return v___x_2433_;
}
else
{
lean_object* v_v_2434_; lean_object* v___x_2435_; lean_object* v_bs_x27_2436_; lean_object* v___x_2437_; 
v_v_2434_ = lean_array_uget(v_bs_2424_, v_i_2423_);
v___x_2435_ = lean_unsigned_to_nat(0u);
v_bs_x27_2436_ = lean_array_uset(v_bs_2424_, v_i_2423_, v___x_2435_);
lean_inc_ref(v_post_2418_);
lean_inc_ref(v_pre_2417_);
v___x_2437_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2417_, v_post_2418_, v_usedLetOnly_2419_, v_skipConstInApp_2420_, v_skipInstances_2421_, v_v_2434_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; size_t v___x_2439_; size_t v___x_2440_; lean_object* v___x_2441_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v___x_2439_ = ((size_t)1ULL);
v___x_2440_ = lean_usize_add(v_i_2423_, v___x_2439_);
v___x_2441_ = lean_array_uset(v_bs_x27_2436_, v_i_2423_, v_a_2438_);
v_i_2423_ = v___x_2440_;
v_bs_2424_ = v___x_2441_;
goto _start;
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec_ref(v_bs_x27_2436_);
lean_dec_ref(v_post_2418_);
lean_dec_ref(v_pre_2417_);
v_a_2443_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2437_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2437_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_2451_, lean_object* v_post_2452_, uint8_t v_usedLetOnly_2453_, uint8_t v_skipConstInApp_2454_, uint8_t v_skipInstances_2455_, lean_object* v___x_2456_, lean_object* v___y_2457_, lean_object* v_b_2458_, lean_object* v_a_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2451_, v_post_2452_, v_usedLetOnly_2453_, v_skipConstInApp_2454_, v_skipInstances_2455_, v___x_2456_, v___y_2457_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2476_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2476_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2476_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
v___x_2471_ = lean_array_fset(v_b_2458_, v_a_2459_, v_a_2467_);
v___x_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v___x_2472_);
v___x_2474_ = v___x_2469_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec_ref(v_b_2458_);
v_a_2477_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2466_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2466_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_2485_, lean_object* v_post_2486_, lean_object* v_usedLetOnly_2487_, lean_object* v_skipConstInApp_2488_, lean_object* v_skipInstances_2489_, lean_object* v___x_2490_, lean_object* v___y_2491_, lean_object* v_b_2492_, lean_object* v_a_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
uint8_t v_usedLetOnly_boxed_2500_; uint8_t v_skipConstInApp_boxed_2501_; uint8_t v_skipInstances_boxed_2502_; lean_object* v_res_2503_; 
v_usedLetOnly_boxed_2500_ = lean_unbox(v_usedLetOnly_2487_);
v_skipConstInApp_boxed_2501_ = lean_unbox(v_skipConstInApp_2488_);
v_skipInstances_boxed_2502_ = lean_unbox(v_skipInstances_2489_);
v_res_2503_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_2485_, v_post_2486_, v_usedLetOnly_boxed_2500_, v_skipConstInApp_boxed_2501_, v_skipInstances_boxed_2502_, v___x_2490_, v___y_2491_, v_b_2492_, v_a_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec(v_a_2493_);
lean_dec(v___y_2491_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_2504_, lean_object* v___x_2505_, lean_object* v_pre_2506_, lean_object* v_post_2507_, uint8_t v_usedLetOnly_2508_, uint8_t v_skipConstInApp_2509_, uint8_t v_skipInstances_2510_, lean_object* v_a_2511_, lean_object* v_b_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v___y_2521_; uint8_t v___x_2544_; 
v___x_2544_ = lean_nat_dec_lt(v_a_2511_, v_upperBound_2504_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; 
lean_dec(v_a_2511_);
lean_dec_ref(v_post_2507_);
lean_dec_ref(v_pre_2506_);
v___x_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2545_, 0, v_b_2512_);
return v___x_2545_;
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; 
v___x_2546_ = lean_array_fget_borrowed(v_b_2512_, v_a_2511_);
v___x_2547_ = lean_array_get_size(v___x_2505_);
v___x_2548_ = lean_nat_dec_lt(v_a_2511_, v___x_2547_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___f_2552_; 
lean_inc(v___x_2546_);
v___x_2549_ = lean_box(v_usedLetOnly_2508_);
v___x_2550_ = lean_box(v_skipConstInApp_2509_);
v___x_2551_ = lean_box(v_skipInstances_2510_);
lean_inc(v_a_2511_);
lean_inc(v___y_2513_);
lean_inc_ref(v_post_2507_);
lean_inc_ref(v_pre_2506_);
v___f_2552_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2552_, 0, v_pre_2506_);
lean_closure_set(v___f_2552_, 1, v_post_2507_);
lean_closure_set(v___f_2552_, 2, v___x_2549_);
lean_closure_set(v___f_2552_, 3, v___x_2550_);
lean_closure_set(v___f_2552_, 4, v___x_2551_);
lean_closure_set(v___f_2552_, 5, v___x_2546_);
lean_closure_set(v___f_2552_, 6, v___y_2513_);
lean_closure_set(v___f_2552_, 7, v_b_2512_);
lean_closure_set(v___f_2552_, 8, v_a_2511_);
v___y_2521_ = v___f_2552_;
goto v___jp_2520_;
}
else
{
lean_object* v___x_2553_; uint8_t v_isInstance_2554_; 
v___x_2553_ = lean_array_fget_borrowed(v___x_2505_, v_a_2511_);
v_isInstance_2554_ = lean_ctor_get_uint8(v___x_2553_, sizeof(void*)*1 + 4);
if (v_isInstance_2554_ == 0)
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___f_2558_; 
lean_inc(v___x_2546_);
v___x_2555_ = lean_box(v_usedLetOnly_2508_);
v___x_2556_ = lean_box(v_skipConstInApp_2509_);
v___x_2557_ = lean_box(v_skipInstances_2510_);
lean_inc(v_a_2511_);
lean_inc(v___y_2513_);
lean_inc_ref(v_post_2507_);
lean_inc_ref(v_pre_2506_);
v___f_2558_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2558_, 0, v_pre_2506_);
lean_closure_set(v___f_2558_, 1, v_post_2507_);
lean_closure_set(v___f_2558_, 2, v___x_2555_);
lean_closure_set(v___f_2558_, 3, v___x_2556_);
lean_closure_set(v___f_2558_, 4, v___x_2557_);
lean_closure_set(v___f_2558_, 5, v___x_2546_);
lean_closure_set(v___f_2558_, 6, v___y_2513_);
lean_closure_set(v___f_2558_, 7, v_b_2512_);
lean_closure_set(v___f_2558_, 8, v_a_2511_);
v___y_2521_ = v___f_2558_;
goto v___jp_2520_;
}
else
{
lean_object* v___x_2559_; lean_object* v___f_2560_; 
v___x_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2559_, 0, v_b_2512_);
v___f_2560_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2560_, 0, v___x_2559_);
v___y_2521_ = v___f_2560_;
goto v___jp_2520_;
}
}
}
v___jp_2520_:
{
lean_object* v___x_2522_; 
lean_inc(v___y_2518_);
lean_inc_ref(v___y_2517_);
lean_inc(v___y_2516_);
lean_inc_ref(v___y_2515_);
lean_inc(v___y_2514_);
v___x_2522_ = lean_apply_6(v___y_2521_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, lean_box(0));
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2535_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2535_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2535_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
if (lean_obj_tag(v_a_2523_) == 0)
{
lean_object* v_a_2527_; lean_object* v___x_2529_; 
lean_dec(v_a_2511_);
lean_dec_ref(v_post_2507_);
lean_dec_ref(v_pre_2506_);
v_a_2527_ = lean_ctor_get(v_a_2523_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v_a_2523_, 1);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v_a_2527_);
v___x_2529_ = v___x_2525_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
lean_del_object(v___x_2525_);
v_a_2531_ = lean_ctor_get(v_a_2523_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v_a_2523_, 1);
v___x_2532_ = lean_unsigned_to_nat(1u);
v___x_2533_ = lean_nat_add(v_a_2511_, v___x_2532_);
lean_dec(v_a_2511_);
v_a_2511_ = v___x_2533_;
v_b_2512_ = v_a_2531_;
goto _start;
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec(v_a_2511_);
lean_dec_ref(v_post_2507_);
lean_dec_ref(v_pre_2506_);
v_a_2536_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2522_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2522_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(uint8_t v_skipInstances_2561_, lean_object* v_pre_2562_, lean_object* v_post_2563_, uint8_t v_usedLetOnly_2564_, uint8_t v_skipConstInApp_2565_, lean_object* v_x_2566_, lean_object* v_x_2567_, lean_object* v_x_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_f_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; 
if (lean_obj_tag(v_x_2566_) == 5)
{
lean_object* v_fn_2626_; lean_object* v_arg_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v_fn_2626_ = lean_ctor_get(v_x_2566_, 0);
lean_inc_ref(v_fn_2626_);
v_arg_2627_ = lean_ctor_get(v_x_2566_, 1);
lean_inc_ref(v_arg_2627_);
lean_dec_ref_known(v_x_2566_, 2);
v___x_2628_ = lean_array_set(v_x_2567_, v_x_2568_, v_arg_2627_);
v___x_2629_ = lean_unsigned_to_nat(1u);
v___x_2630_ = lean_nat_sub(v_x_2568_, v___x_2629_);
lean_dec(v_x_2568_);
v_x_2566_ = v_fn_2626_;
v_x_2567_ = v___x_2628_;
v_x_2568_ = v___x_2630_;
goto _start;
}
else
{
lean_dec(v_x_2568_);
if (v_skipConstInApp_2565_ == 0)
{
goto v___jp_2623_;
}
else
{
uint8_t v___x_2632_; 
v___x_2632_ = l_Lean_Expr_isConst(v_x_2566_);
if (v___x_2632_ == 0)
{
goto v___jp_2623_;
}
else
{
v_f_2577_ = v_x_2566_;
v___y_2578_ = v___y_2569_;
v___y_2579_ = v___y_2570_;
v___y_2580_ = v___y_2571_;
v___y_2581_ = v___y_2572_;
v___y_2582_ = v___y_2573_;
v___y_2583_ = v___y_2574_;
goto v___jp_2576_;
}
}
}
v___jp_2576_:
{
if (v_skipInstances_2561_ == 0)
{
size_t v_sz_2584_; size_t v___x_2585_; lean_object* v___x_2586_; 
v_sz_2584_ = lean_array_size(v_x_2567_);
v___x_2585_ = ((size_t)0ULL);
lean_inc_ref(v_post_2563_);
lean_inc_ref(v_pre_2562_);
v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2562_, v_post_2563_, v_usedLetOnly_2564_, v_skipConstInApp_2565_, v_skipInstances_2561_, v_sz_2584_, v___x_2585_, v_x_2567_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2586_, 1);
v___x_2588_ = l_Lean_mkAppN(v_f_2577_, v_a_2587_);
lean_dec(v_a_2587_);
v___x_2589_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2562_, v_post_2563_, v_usedLetOnly_2564_, v_skipConstInApp_2565_, v_skipInstances_2561_, v___x_2588_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2589_;
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec_ref(v_f_2577_);
lean_dec_ref(v_post_2563_);
lean_dec_ref(v_pre_2562_);
v_a_2590_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2586_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2586_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
else
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = lean_array_get_size(v_x_2567_);
lean_inc_ref(v_f_2577_);
v___x_2599_ = l_Lean_Meta_getFunInfoNArgs(v_f_2577_, v___x_2598_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v_paramInfo_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
lean_dec_ref_known(v___x_2599_, 1);
v_paramInfo_2601_ = lean_ctor_get(v_a_2600_, 0);
lean_inc_ref(v_paramInfo_2601_);
lean_dec(v_a_2600_);
v___x_2602_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2563_);
lean_inc_ref(v_pre_2562_);
v___x_2603_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v___x_2598_, v_paramInfo_2601_, v_pre_2562_, v_post_2563_, v_usedLetOnly_2564_, v_skipConstInApp_2565_, v_skipInstances_2561_, v___x_2602_, v_x_2567_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec_ref(v_paramInfo_2601_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
v___x_2605_ = l_Lean_mkAppN(v_f_2577_, v_a_2604_);
lean_dec(v_a_2604_);
v___x_2606_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2562_, v_post_2563_, v_usedLetOnly_2564_, v_skipConstInApp_2565_, v_skipInstances_2561_, v___x_2605_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2606_;
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec_ref(v_f_2577_);
lean_dec_ref(v_post_2563_);
lean_dec_ref(v_pre_2562_);
v_a_2607_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2603_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2603_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec_ref(v_f_2577_);
lean_dec_ref(v_x_2567_);
lean_dec_ref(v_post_2563_);
lean_dec_ref(v_pre_2562_);
v_a_2615_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2599_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2599_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
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
}
v___jp_2623_:
{
lean_object* v___x_2624_; 
lean_inc_ref(v_post_2563_);
lean_inc_ref(v_pre_2562_);
v___x_2624_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2562_, v_post_2563_, v_usedLetOnly_2564_, v_skipConstInApp_2565_, v_skipInstances_2561_, v_x_2566_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___x_2624_, 1);
v_f_2577_ = v_a_2625_;
v___y_2578_ = v___y_2569_;
v___y_2579_ = v___y_2570_;
v___y_2580_ = v___y_2571_;
v___y_2581_ = v___y_2572_;
v___y_2582_ = v___y_2573_;
v___y_2583_ = v___y_2574_;
goto v___jp_2576_;
}
else
{
lean_dec_ref(v_x_2567_);
lean_dec_ref(v_post_2563_);
lean_dec_ref(v_pre_2562_);
return v___x_2624_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(lean_object* v___x_2633_, lean_object* v_pre_2634_, lean_object* v_e_2635_, lean_object* v_post_2636_, uint8_t v_usedLetOnly_2637_, uint8_t v_skipConstInApp_2638_, uint8_t v_skipInstances_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_Core_checkSystem(v___x_2633_, v___y_2644_, v___y_2645_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v___x_2648_; 
lean_dec_ref_known(v___x_2647_, 1);
lean_inc_ref(v_pre_2634_);
lean_inc(v___y_2645_);
lean_inc_ref(v___y_2644_);
lean_inc(v___y_2643_);
lean_inc_ref(v___y_2642_);
lean_inc(v___y_2641_);
lean_inc_ref(v_e_2635_);
v___x_2648_ = lean_apply_7(v_pre_2634_, v_e_2635_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, lean_box(0));
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2697_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2651_ = v___x_2648_;
v_isShared_2652_ = v_isSharedCheck_2697_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2697_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___y_2654_; 
switch(lean_obj_tag(v_a_2649_))
{
case 0:
{
lean_object* v_e_2689_; lean_object* v___x_2691_; 
lean_dec_ref(v_post_2636_);
lean_dec_ref(v_e_2635_);
lean_dec_ref(v_pre_2634_);
v_e_2689_ = lean_ctor_get(v_a_2649_, 0);
lean_inc_ref(v_e_2689_);
lean_dec_ref_known(v_a_2649_, 1);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v_e_2689_);
v___x_2691_ = v___x_2651_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_e_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
case 1:
{
lean_object* v_e_2693_; lean_object* v___x_2694_; 
lean_del_object(v___x_2651_);
lean_dec_ref(v_e_2635_);
v_e_2693_ = lean_ctor_get(v_a_2649_, 0);
lean_inc_ref(v_e_2693_);
lean_dec_ref_known(v_a_2649_, 1);
v___x_2694_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2634_, v_post_2636_, v_usedLetOnly_2637_, v_skipConstInApp_2638_, v_skipInstances_2639_, v_e_2693_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2694_;
}
default: 
{
lean_object* v_e_x3f_2695_; 
lean_del_object(v___x_2651_);
v_e_x3f_2695_ = lean_ctor_get(v_a_2649_, 0);
lean_inc(v_e_x3f_2695_);
lean_dec_ref_known(v_a_2649_, 1);
if (lean_obj_tag(v_e_x3f_2695_) == 0)
{
v___y_2654_ = v_e_2635_;
goto v___jp_2653_;
}
else
{
lean_object* v_val_2696_; 
lean_dec_ref(v_e_2635_);
v_val_2696_ = lean_ctor_get(v_e_x3f_2695_, 0);
lean_inc(v_val_2696_);
lean_dec_ref_known(v_e_x3f_2695_, 1);
v___y_2654_ = v_val_2696_;
goto v___jp_2653_;
}
}
}
v___jp_2653_:
{
switch(lean_obj_tag(v___y_2654_))
{
case 7:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2656_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2634_, v_post_2636_, v_usedLetOnly_2637_, v_skipConstInApp_2638_, v_skipInstances_2639_, v___x_2655_, v___y_2654_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2656_;
}
case 6:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2658_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2634_, v_post_2636_, v_usedLetOnly_2637_, v_skipConstInApp_2638_, v_skipInstances_2639_, v___x_2657_, v___y_2654_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2658_;
}
case 8:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2660_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2634_, v_post_2636_, v_usedLetOnly_2637_, v_skipConstInApp_2638_, v_skipInstances_2639_, v___x_2659_, v___y_2654_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2660_;
}
case 5:
{
lean_object* v_dummy_2661_; lean_object* v_nargs_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_dummy_2661_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1);
v_nargs_2662_ = l_Lean_Expr_getAppNumArgs(v___y_2654_);
lean_inc(v_nargs_2662_);
v___x_2663_ = lean_mk_array(v_nargs_2662_, v_dummy_2661_);
v___x_2664_ = lean_unsigned_to_nat(1u);
v___x_2665_ = lean_nat_sub(v_nargs_2662_, v___x_2664_);
lean_dec(v_nargs_2662_);
v___x_2666_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_2639_, v_pre_2634_, v_post_2636_, v_usedLetOnly_2637_, v_skipConstInApp_2638_, v___y_2654_, v___x_2663_, v___x_2665_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2666_;
}
case 10:
{
lean_object* v_data_2667_; lean_object* v_expr_2668_; lean_object* v___x_2669_; 
v_data_2667_ = lean_ctor_get(v___y_2654_, 0);
v_expr_2668_ = lean_ctor_get(v___y_2654_, 1);
lean_inc_ref(v_expr_2668_);
lean_inc_ref(v_post_2636_);
lean_inc_ref(v_pre_2634_);
v___x_2669_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2634_, v_post_2636_, v_usedLetOnly_2637_, v_skipConstInApp_2638_, v_skipInstances_2639_, v_expr_2668_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; size_t v___x_2671_; size_t v___x_2672_; uint8_t v___x_2673_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2669_, 1);
v___x_2671_ = lean_ptr_addr(v_expr_2668_);
v___x_2672_ = lean_ptr_addr(v_a_2670_);
v___x_2673_ = lean_usize_dec_eq(v___x_2671_, v___x_2672_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
lean_inc(v_data_2667_);
lean_dec_ref_known(v___y_2654_, 2);
v___x_2674_ = l_Lean_Expr_mdata___override(v_data_2667_, v_a_2670_);
v___x_2675_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2634_, v_post_2636_, v_usedLetOnly_2637_, v_skipConstInApp_2638_, v_skipInstances_2639_, v___x_2674_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2675_;
}
else
{
lean_object* v___x_2676_; 
lean_dec(v_a_2670_);
v___x_2676_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2634_, v_post_2636_, v_usedLetOnly_2637_, v_skipConstInApp_2638_, v_skipInstances_2639_, v___y_2654_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2676_;
}
}
else
{
lean_dec_ref_known(v___y_2654_, 2);
lean_dec_ref(v_post_2636_);
lean_dec_ref(v_pre_2634_);
return v___x_2669_;
}
}
case 11:
{
lean_object* v_typeName_2677_; lean_object* v_idx_2678_; lean_object* v_struct_2679_; lean_object* v___x_2680_; 
v_typeName_2677_ = lean_ctor_get(v___y_2654_, 0);
v_idx_2678_ = lean_ctor_get(v___y_2654_, 1);
v_struct_2679_ = lean_ctor_get(v___y_2654_, 2);
lean_inc_ref(v_struct_2679_);
lean_inc_ref(v_post_2636_);
lean_inc_ref(v_pre_2634_);
v___x_2680_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2634_, v_post_2636_, v_usedLetOnly_2637_, v_skipConstInApp_2638_, v_skipInstances_2639_, v_struct_2679_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; size_t v___x_2682_; size_t v___x_2683_; uint8_t v___x_2684_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2682_ = lean_ptr_addr(v_struct_2679_);
v___x_2683_ = lean_ptr_addr(v_a_2681_);
v___x_2684_ = lean_usize_dec_eq(v___x_2682_, v___x_2683_);
if (v___x_2684_ == 0)
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
lean_inc(v_idx_2678_);
lean_inc(v_typeName_2677_);
lean_dec_ref_known(v___y_2654_, 3);
v___x_2685_ = l_Lean_Expr_proj___override(v_typeName_2677_, v_idx_2678_, v_a_2681_);
v___x_2686_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2634_, v_post_2636_, v_usedLetOnly_2637_, v_skipConstInApp_2638_, v_skipInstances_2639_, v___x_2685_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2686_;
}
else
{
lean_object* v___x_2687_; 
lean_dec(v_a_2681_);
v___x_2687_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2634_, v_post_2636_, v_usedLetOnly_2637_, v_skipConstInApp_2638_, v_skipInstances_2639_, v___y_2654_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2687_;
}
}
else
{
lean_dec_ref_known(v___y_2654_, 3);
lean_dec_ref(v_post_2636_);
lean_dec_ref(v_pre_2634_);
return v___x_2680_;
}
}
default: 
{
lean_object* v___x_2688_; 
v___x_2688_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2634_, v_post_2636_, v_usedLetOnly_2637_, v_skipConstInApp_2638_, v_skipInstances_2639_, v___y_2654_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2688_;
}
}
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec_ref(v_post_2636_);
lean_dec_ref(v_e_2635_);
lean_dec_ref(v_pre_2634_);
v_a_2698_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2648_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2648_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec_ref(v_post_2636_);
lean_dec_ref(v_e_2635_);
lean_dec_ref(v_pre_2634_);
v_a_2706_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2647_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2647_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(lean_object* v___x_2714_, lean_object* v_pre_2715_, lean_object* v_e_2716_, lean_object* v_post_2717_, lean_object* v_usedLetOnly_2718_, lean_object* v_skipConstInApp_2719_, lean_object* v_skipInstances_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
uint8_t v_usedLetOnly_boxed_2728_; uint8_t v_skipConstInApp_boxed_2729_; uint8_t v_skipInstances_boxed_2730_; lean_object* v_res_2731_; 
v_usedLetOnly_boxed_2728_ = lean_unbox(v_usedLetOnly_2718_);
v_skipConstInApp_boxed_2729_ = lean_unbox(v_skipConstInApp_2719_);
v_skipInstances_boxed_2730_ = lean_unbox(v_skipInstances_2720_);
v_res_2731_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(v___x_2714_, v_pre_2715_, v_e_2716_, v_post_2717_, v_usedLetOnly_boxed_2728_, v_skipConstInApp_boxed_2729_, v_skipInstances_boxed_2730_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec(v___y_2721_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(lean_object* v_pre_2732_, lean_object* v_post_2733_, uint8_t v_usedLetOnly_2734_, uint8_t v_skipConstInApp_2735_, uint8_t v_skipInstances_2736_, lean_object* v_e_2737_, lean_object* v_a_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_inc(v_a_2738_);
v___x_2745_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2745_, 0, lean_box(0));
lean_closure_set(v___x_2745_, 1, lean_box(0));
lean_closure_set(v___x_2745_, 2, v_a_2738_);
v___x_2746_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___x_2745_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2781_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2781_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2781_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_a_2747_, v_e_2737_);
lean_dec(v_a_2747_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___f_2756_; lean_object* v___x_2757_; 
lean_del_object(v___x_2749_);
v___x_2752_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0));
v___x_2753_ = lean_box(v_usedLetOnly_2734_);
v___x_2754_ = lean_box(v_skipConstInApp_2735_);
v___x_2755_ = lean_box(v_skipInstances_2736_);
lean_inc_ref(v_e_2737_);
v___f_2756_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed), 14, 7);
lean_closure_set(v___f_2756_, 0, v___x_2752_);
lean_closure_set(v___f_2756_, 1, v_pre_2732_);
lean_closure_set(v___f_2756_, 2, v_e_2737_);
lean_closure_set(v___f_2756_, 3, v_post_2733_);
lean_closure_set(v___f_2756_, 4, v___x_2753_);
lean_closure_set(v___f_2756_, 5, v___x_2754_);
lean_closure_set(v___f_2756_, 6, v___x_2755_);
v___x_2757_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v___f_2756_, v_a_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___f_2759_; lean_object* v___x_2760_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc_n(v_a_2758_, 2);
lean_dec_ref_known(v___x_2757_, 1);
lean_inc(v_a_2738_);
v___f_2759_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2759_, 0, v_a_2738_);
lean_closure_set(v___f_2759_, 1, v_e_2737_);
lean_closure_set(v___f_2759_, 2, v_a_2758_);
v___x_2760_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___f_2759_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2767_ == 0)
{
lean_object* v_unused_2768_; 
v_unused_2768_ = lean_ctor_get(v___x_2760_, 0);
lean_dec(v_unused_2768_);
v___x_2762_ = v___x_2760_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_dec(v___x_2760_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v_a_2758_);
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2758_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec(v_a_2758_);
v_a_2769_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2760_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2760_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
else
{
lean_dec_ref(v_e_2737_);
return v___x_2757_;
}
}
else
{
lean_object* v_val_2777_; lean_object* v___x_2779_; 
lean_dec_ref(v_e_2737_);
lean_dec_ref(v_post_2733_);
lean_dec_ref(v_pre_2732_);
v_val_2777_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_val_2777_);
lean_dec_ref_known(v___x_2751_, 1);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v_val_2777_);
v___x_2779_ = v___x_2749_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_val_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec_ref(v_e_2737_);
lean_dec_ref(v_post_2733_);
lean_dec_ref(v_pre_2732_);
v_a_2782_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2746_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2746_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object* v_pre_2790_, lean_object* v_post_2791_, uint8_t v_usedLetOnly_2792_, uint8_t v_skipConstInApp_2793_, uint8_t v_skipInstances_2794_, lean_object* v_fvars_2795_, lean_object* v_e_2796_, lean_object* v_a_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
if (lean_obj_tag(v_e_2796_) == 7)
{
lean_object* v_binderName_2804_; lean_object* v_binderType_2805_; lean_object* v_body_2806_; uint8_t v_binderInfo_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___f_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_binderName_2804_ = lean_ctor_get(v_e_2796_, 0);
lean_inc(v_binderName_2804_);
v_binderType_2805_ = lean_ctor_get(v_e_2796_, 1);
lean_inc_ref(v_binderType_2805_);
v_body_2806_ = lean_ctor_get(v_e_2796_, 2);
lean_inc_ref(v_body_2806_);
v_binderInfo_2807_ = lean_ctor_get_uint8(v_e_2796_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2796_, 3);
v___x_2808_ = lean_box(v_usedLetOnly_2792_);
v___x_2809_ = lean_box(v_skipConstInApp_2793_);
v___x_2810_ = lean_box(v_skipInstances_2794_);
lean_inc_ref(v_post_2791_);
lean_inc_ref(v_pre_2790_);
lean_inc_ref(v_fvars_2795_);
v___f_2811_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2811_, 0, v_fvars_2795_);
lean_closure_set(v___f_2811_, 1, v_pre_2790_);
lean_closure_set(v___f_2811_, 2, v_post_2791_);
lean_closure_set(v___f_2811_, 3, v___x_2808_);
lean_closure_set(v___f_2811_, 4, v___x_2809_);
lean_closure_set(v___f_2811_, 5, v___x_2810_);
lean_closure_set(v___f_2811_, 6, v_body_2806_);
v___x_2812_ = lean_expr_instantiate_rev(v_binderType_2805_, v_fvars_2795_);
lean_dec_ref(v_fvars_2795_);
lean_dec_ref(v_binderType_2805_);
v___x_2813_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2790_, v_post_2791_, v_usedLetOnly_2792_, v_skipConstInApp_2793_, v_skipInstances_2794_, v___x_2812_, v_a_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; uint8_t v___x_2815_; lean_object* v___x_2816_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2813_, 1);
v___x_2815_ = 0;
v___x_2816_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2804_, v_binderInfo_2807_, v_a_2814_, v___f_2811_, v___x_2815_, v_a_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
return v___x_2816_;
}
else
{
lean_dec_ref(v___f_2811_);
lean_dec(v_binderName_2804_);
return v___x_2813_;
}
}
else
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = lean_expr_instantiate_rev(v_e_2796_, v_fvars_2795_);
lean_dec_ref(v_e_2796_);
lean_inc_ref(v_post_2791_);
lean_inc_ref(v_pre_2790_);
v___x_2818_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2790_, v_post_2791_, v_usedLetOnly_2792_, v_skipConstInApp_2793_, v_skipInstances_2794_, v___x_2817_, v_a_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; uint8_t v___x_2820_; uint8_t v___x_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
v___x_2820_ = 0;
v___x_2821_ = 1;
v___x_2822_ = 1;
v___x_2823_ = l_Lean_Meta_mkForallFVars(v_fvars_2795_, v_a_2819_, v___x_2820_, v_usedLetOnly_2792_, v___x_2821_, v___x_2822_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec_ref(v_fvars_2795_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2825_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
v___x_2825_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2790_, v_post_2791_, v_usedLetOnly_2792_, v_skipConstInApp_2793_, v_skipInstances_2794_, v_a_2824_, v_a_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
return v___x_2825_;
}
else
{
lean_dec_ref(v_post_2791_);
lean_dec_ref(v_pre_2790_);
return v___x_2823_;
}
}
else
{
lean_dec_ref(v_fvars_2795_);
lean_dec_ref(v_post_2791_);
lean_dec_ref(v_pre_2790_);
return v___x_2818_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_2826_, lean_object* v_pre_2827_, lean_object* v_post_2828_, uint8_t v_usedLetOnly_2829_, uint8_t v_skipConstInApp_2830_, uint8_t v_skipInstances_2831_, lean_object* v_body_2832_, lean_object* v_x_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = lean_array_push(v_fvars_2826_, v_x_2833_);
v___x_2842_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2827_, v_post_2828_, v_usedLetOnly_2829_, v_skipConstInApp_2830_, v_skipInstances_2831_, v___x_2841_, v_body_2832_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2843_, lean_object* v_post_2844_, lean_object* v_usedLetOnly_2845_, lean_object* v_skipConstInApp_2846_, lean_object* v_skipInstances_2847_, lean_object* v_e_2848_, lean_object* v_a_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
uint8_t v_usedLetOnly_boxed_2856_; uint8_t v_skipConstInApp_boxed_2857_; uint8_t v_skipInstances_boxed_2858_; lean_object* v_res_2859_; 
v_usedLetOnly_boxed_2856_ = lean_unbox(v_usedLetOnly_2845_);
v_skipConstInApp_boxed_2857_ = lean_unbox(v_skipConstInApp_2846_);
v_skipInstances_boxed_2858_ = lean_unbox(v_skipInstances_2847_);
v_res_2859_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2843_, v_post_2844_, v_usedLetOnly_boxed_2856_, v_skipConstInApp_boxed_2857_, v_skipInstances_boxed_2858_, v_e_2848_, v_a_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec(v_a_2849_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_2860_, lean_object* v_post_2861_, lean_object* v_usedLetOnly_2862_, lean_object* v_skipConstInApp_2863_, lean_object* v_skipInstances_2864_, lean_object* v_sz_2865_, lean_object* v_i_2866_, lean_object* v_bs_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
uint8_t v_usedLetOnly_boxed_2875_; uint8_t v_skipConstInApp_boxed_2876_; uint8_t v_skipInstances_boxed_2877_; size_t v_sz_boxed_2878_; size_t v_i_boxed_2879_; lean_object* v_res_2880_; 
v_usedLetOnly_boxed_2875_ = lean_unbox(v_usedLetOnly_2862_);
v_skipConstInApp_boxed_2876_ = lean_unbox(v_skipConstInApp_2863_);
v_skipInstances_boxed_2877_ = lean_unbox(v_skipInstances_2864_);
v_sz_boxed_2878_ = lean_unbox_usize(v_sz_2865_);
lean_dec(v_sz_2865_);
v_i_boxed_2879_ = lean_unbox_usize(v_i_2866_);
lean_dec(v_i_2866_);
v_res_2880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2860_, v_post_2861_, v_usedLetOnly_boxed_2875_, v_skipConstInApp_boxed_2876_, v_skipInstances_boxed_2877_, v_sz_boxed_2878_, v_i_boxed_2879_, v_bs_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v___y_2868_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object* v_pre_2881_, lean_object* v_post_2882_, lean_object* v_usedLetOnly_2883_, lean_object* v_skipConstInApp_2884_, lean_object* v_skipInstances_2885_, lean_object* v_e_2886_, lean_object* v_a_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
uint8_t v_usedLetOnly_boxed_2894_; uint8_t v_skipConstInApp_boxed_2895_; uint8_t v_skipInstances_boxed_2896_; lean_object* v_res_2897_; 
v_usedLetOnly_boxed_2894_ = lean_unbox(v_usedLetOnly_2883_);
v_skipConstInApp_boxed_2895_ = lean_unbox(v_skipConstInApp_2884_);
v_skipInstances_boxed_2896_ = lean_unbox(v_skipInstances_2885_);
v_res_2897_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2881_, v_post_2882_, v_usedLetOnly_boxed_2894_, v_skipConstInApp_boxed_2895_, v_skipInstances_boxed_2896_, v_e_2886_, v_a_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec(v_a_2887_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_2898_, lean_object* v_post_2899_, lean_object* v_usedLetOnly_2900_, lean_object* v_skipConstInApp_2901_, lean_object* v_skipInstances_2902_, lean_object* v_fvars_2903_, lean_object* v_e_2904_, lean_object* v_a_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
uint8_t v_usedLetOnly_boxed_2912_; uint8_t v_skipConstInApp_boxed_2913_; uint8_t v_skipInstances_boxed_2914_; lean_object* v_res_2915_; 
v_usedLetOnly_boxed_2912_ = lean_unbox(v_usedLetOnly_2900_);
v_skipConstInApp_boxed_2913_ = lean_unbox(v_skipConstInApp_2901_);
v_skipInstances_boxed_2914_ = lean_unbox(v_skipInstances_2902_);
v_res_2915_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2898_, v_post_2899_, v_usedLetOnly_boxed_2912_, v_skipConstInApp_boxed_2913_, v_skipInstances_boxed_2914_, v_fvars_2903_, v_e_2904_, v_a_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec(v_a_2905_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_2916_, lean_object* v_post_2917_, lean_object* v_usedLetOnly_2918_, lean_object* v_skipConstInApp_2919_, lean_object* v_skipInstances_2920_, lean_object* v_fvars_2921_, lean_object* v_e_2922_, lean_object* v_a_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
uint8_t v_usedLetOnly_boxed_2930_; uint8_t v_skipConstInApp_boxed_2931_; uint8_t v_skipInstances_boxed_2932_; lean_object* v_res_2933_; 
v_usedLetOnly_boxed_2930_ = lean_unbox(v_usedLetOnly_2918_);
v_skipConstInApp_boxed_2931_ = lean_unbox(v_skipConstInApp_2919_);
v_skipInstances_boxed_2932_ = lean_unbox(v_skipInstances_2920_);
v_res_2933_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2916_, v_post_2917_, v_usedLetOnly_boxed_2930_, v_skipConstInApp_boxed_2931_, v_skipInstances_boxed_2932_, v_fvars_2921_, v_e_2922_, v_a_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec(v_a_2923_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_2934_, lean_object* v_post_2935_, lean_object* v_usedLetOnly_2936_, lean_object* v_skipConstInApp_2937_, lean_object* v_skipInstances_2938_, lean_object* v_fvars_2939_, lean_object* v_e_2940_, lean_object* v_a_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
uint8_t v_usedLetOnly_boxed_2948_; uint8_t v_skipConstInApp_boxed_2949_; uint8_t v_skipInstances_boxed_2950_; lean_object* v_res_2951_; 
v_usedLetOnly_boxed_2948_ = lean_unbox(v_usedLetOnly_2936_);
v_skipConstInApp_boxed_2949_ = lean_unbox(v_skipConstInApp_2937_);
v_skipInstances_boxed_2950_ = lean_unbox(v_skipInstances_2938_);
v_res_2951_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2934_, v_post_2935_, v_usedLetOnly_boxed_2948_, v_skipConstInApp_boxed_2949_, v_skipInstances_boxed_2950_, v_fvars_2939_, v_e_2940_, v_a_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v_a_2941_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_2952_, lean_object* v___x_2953_, lean_object* v_pre_2954_, lean_object* v_post_2955_, lean_object* v_usedLetOnly_2956_, lean_object* v_skipConstInApp_2957_, lean_object* v_skipInstances_2958_, lean_object* v_a_2959_, lean_object* v_b_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
uint8_t v_usedLetOnly_boxed_2968_; uint8_t v_skipConstInApp_boxed_2969_; uint8_t v_skipInstances_boxed_2970_; lean_object* v_res_2971_; 
v_usedLetOnly_boxed_2968_ = lean_unbox(v_usedLetOnly_2956_);
v_skipConstInApp_boxed_2969_ = lean_unbox(v_skipConstInApp_2957_);
v_skipInstances_boxed_2970_ = lean_unbox(v_skipInstances_2958_);
v_res_2971_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_2952_, v___x_2953_, v_pre_2954_, v_post_2955_, v_usedLetOnly_boxed_2968_, v_skipConstInApp_boxed_2969_, v_skipInstances_boxed_2970_, v_a_2959_, v_b_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___x_2953_);
lean_dec(v_upperBound_2952_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_2972_, lean_object* v_pre_2973_, lean_object* v_post_2974_, lean_object* v_usedLetOnly_2975_, lean_object* v_skipConstInApp_2976_, lean_object* v_x_2977_, lean_object* v_x_2978_, lean_object* v_x_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
uint8_t v_skipInstances_boxed_2987_; uint8_t v_usedLetOnly_boxed_2988_; uint8_t v_skipConstInApp_boxed_2989_; lean_object* v_res_2990_; 
v_skipInstances_boxed_2987_ = lean_unbox(v_skipInstances_2972_);
v_usedLetOnly_boxed_2988_ = lean_unbox(v_usedLetOnly_2975_);
v_skipConstInApp_boxed_2989_ = lean_unbox(v_skipConstInApp_2976_);
v_res_2990_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_boxed_2987_, v_pre_2973_, v_post_2974_, v_usedLetOnly_boxed_2988_, v_skipConstInApp_boxed_2989_, v_x_2977_, v_x_2978_, v_x_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec(v___y_2980_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object* v_00_u03b1_2991_, lean_object* v_x_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = lean_apply_1(v_x_2992_, lean_box(0));
v___x_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3001_, lean_object* v_x_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(v_00_u03b1_3001_, v_x_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
return v_res_3009_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3010_ = lean_box(0);
v___x_3011_ = lean_unsigned_to_nat(16u);
v___x_3012_ = lean_mk_array(v___x_3011_, v___x_3010_);
return v___x_3012_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0);
v___x_3014_ = lean_unsigned_to_nat(0u);
v___x_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
lean_ctor_set(v___x_3015_, 1, v___x_3013_);
return v___x_3015_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1);
v___x_3017_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3017_, 0, lean_box(0));
lean_closure_set(v___x_3017_, 1, lean_box(0));
lean_closure_set(v___x_3017_, 2, v___x_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object* v_input_3018_, lean_object* v_pre_3019_, lean_object* v_post_3020_, uint8_t v_usedLetOnly_3021_, uint8_t v_skipConstInApp_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
uint8_t v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v_a_3032_; lean_object* v___x_3033_; 
v___x_3029_ = 0;
v___x_3030_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2);
v___x_3031_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3030_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref(v___x_3031_);
v___x_3033_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_3019_, v_post_3020_, v_usedLetOnly_3021_, v_skipConstInApp_3022_, v___x_3029_, v_input_3018_, v_a_3032_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___x_3033_, 1);
v___x_3035_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3035_, 0, lean_box(0));
lean_closure_set(v___x_3035_, 1, lean_box(0));
lean_closure_set(v___x_3035_, 2, v_a_3032_);
v___x_3036_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3035_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3043_ == 0)
{
lean_object* v_unused_3044_; 
v_unused_3044_ = lean_ctor_get(v___x_3036_, 0);
lean_dec(v_unused_3044_);
v___x_3038_ = v___x_3036_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_dec(v___x_3036_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v_a_3034_);
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3034_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
else
{
lean_dec(v_a_3032_);
return v___x_3033_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object* v_input_3045_, lean_object* v_pre_3046_, lean_object* v_post_3047_, lean_object* v_usedLetOnly_3048_, lean_object* v_skipConstInApp_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
uint8_t v_usedLetOnly_boxed_3056_; uint8_t v_skipConstInApp_boxed_3057_; lean_object* v_res_3058_; 
v_usedLetOnly_boxed_3056_ = lean_unbox(v_usedLetOnly_3048_);
v_skipConstInApp_boxed_3057_ = lean_unbox(v_skipConstInApp_3049_);
v_res_3058_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_input_3045_, v_pre_3046_, v_post_3047_, v_usedLetOnly_boxed_3056_, v_skipConstInApp_boxed_3057_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object* v_e_3060_, uint8_t v_elimTrivial_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v___x_3067_; lean_object* v_pre_3068_; lean_object* v___f_3069_; uint8_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3067_ = lean_box(v_elimTrivial_3061_);
v_pre_3068_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed), 8, 1);
lean_closure_set(v_pre_3068_, 0, v___x_3067_);
v___f_3069_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0));
v___x_3070_ = 0;
v___x_3071_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_3072_ = lean_st_mk_ref(v___x_3071_);
v___x_3073_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_e_3060_, v_pre_3068_, v___f_3069_, v___x_3070_, v___x_3070_, v___x_3072_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3082_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3076_ = v___x_3073_;
v_isShared_3077_ = v_isSharedCheck_3082_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3073_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3082_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3078_; lean_object* v___x_3080_; 
v___x_3078_ = lean_st_ref_get(v___x_3072_);
lean_dec(v___x_3072_);
lean_dec(v___x_3078_);
if (v_isShared_3077_ == 0)
{
v___x_3080_ = v___x_3076_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3074_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
else
{
lean_dec(v___x_3072_);
return v___x_3073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object* v_e_3083_, lean_object* v_elimTrivial_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_){
_start:
{
uint8_t v_elimTrivial_boxed_3090_; lean_object* v_res_3091_; 
v_elimTrivial_boxed_3090_ = lean_unbox(v_elimTrivial_3084_);
v_res_3091_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v_e_3083_, v_elimTrivial_boxed_3090_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object* v_upperBound_3092_, lean_object* v___x_3093_, lean_object* v_pre_3094_, lean_object* v_post_3095_, uint8_t v_usedLetOnly_3096_, uint8_t v_skipConstInApp_3097_, uint8_t v_skipInstances_3098_, lean_object* v___x_3099_, lean_object* v_inst_3100_, lean_object* v_R_3101_, lean_object* v_a_3102_, lean_object* v_b_3103_, lean_object* v_c_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v___x_3112_; 
v___x_3112_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_3092_, v___x_3093_, v_pre_3094_, v_post_3095_, v_usedLetOnly_3096_, v_skipConstInApp_3097_, v_skipInstances_3098_, v_a_3102_, v_b_3103_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_3113_ = _args[0];
lean_object* v___x_3114_ = _args[1];
lean_object* v_pre_3115_ = _args[2];
lean_object* v_post_3116_ = _args[3];
lean_object* v_usedLetOnly_3117_ = _args[4];
lean_object* v_skipConstInApp_3118_ = _args[5];
lean_object* v_skipInstances_3119_ = _args[6];
lean_object* v___x_3120_ = _args[7];
lean_object* v_inst_3121_ = _args[8];
lean_object* v_R_3122_ = _args[9];
lean_object* v_a_3123_ = _args[10];
lean_object* v_b_3124_ = _args[11];
lean_object* v_c_3125_ = _args[12];
lean_object* v___y_3126_ = _args[13];
lean_object* v___y_3127_ = _args[14];
lean_object* v___y_3128_ = _args[15];
lean_object* v___y_3129_ = _args[16];
lean_object* v___y_3130_ = _args[17];
lean_object* v___y_3131_ = _args[18];
lean_object* v___y_3132_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_3133_; uint8_t v_skipConstInApp_boxed_3134_; uint8_t v_skipInstances_boxed_3135_; lean_object* v_res_3136_; 
v_usedLetOnly_boxed_3133_ = lean_unbox(v_usedLetOnly_3117_);
v_skipConstInApp_boxed_3134_ = lean_unbox(v_skipConstInApp_3118_);
v_skipInstances_boxed_3135_ = lean_unbox(v_skipInstances_3119_);
v_res_3136_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_upperBound_3113_, v___x_3114_, v_pre_3115_, v_post_3116_, v_usedLetOnly_boxed_3133_, v_skipConstInApp_boxed_3134_, v_skipInstances_boxed_3135_, v___x_3120_, v_inst_3121_, v_R_3122_, v_a_3123_, v_b_3124_, v_c_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec(v___x_3120_);
lean_dec_ref(v___x_3114_);
lean_dec(v_upperBound_3113_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3137_, lean_object* v_m_3138_, lean_object* v_a_3139_){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_3138_, v_a_3139_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_3141_, lean_object* v_m_3142_, lean_object* v_a_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(v_00_u03b2_3141_, v_m_3142_, v_a_3143_);
lean_dec_ref(v_a_3143_);
lean_dec_ref(v_m_3142_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_3145_, lean_object* v_name_3146_, uint8_t v_bi_3147_, lean_object* v_type_3148_, lean_object* v_k_3149_, uint8_t v_kind_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v___x_3158_; 
v___x_3158_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_3146_, v_bi_3147_, v_type_3148_, v_k_3149_, v_kind_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3159_, lean_object* v_name_3160_, lean_object* v_bi_3161_, lean_object* v_type_3162_, lean_object* v_k_3163_, lean_object* v_kind_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
uint8_t v_bi_boxed_3172_; uint8_t v_kind_boxed_3173_; lean_object* v_res_3174_; 
v_bi_boxed_3172_ = lean_unbox(v_bi_3161_);
v_kind_boxed_3173_ = lean_unbox(v_kind_3164_);
v_res_3174_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_3159_, v_name_3160_, v_bi_boxed_3172_, v_type_3162_, v_k_3163_, v_kind_boxed_3173_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec(v___y_3165_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_3175_, lean_object* v_name_3176_, lean_object* v_type_3177_, lean_object* v_val_3178_, lean_object* v_k_3179_, uint8_t v_nondep_3180_, uint8_t v_kind_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v___x_3189_; 
v___x_3189_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_3176_, v_type_3177_, v_val_3178_, v_k_3179_, v_nondep_3180_, v_kind_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_3190_, lean_object* v_name_3191_, lean_object* v_type_3192_, lean_object* v_val_3193_, lean_object* v_k_3194_, lean_object* v_nondep_3195_, lean_object* v_kind_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
uint8_t v_nondep_boxed_3204_; uint8_t v_kind_boxed_3205_; lean_object* v_res_3206_; 
v_nondep_boxed_3204_ = lean_unbox(v_nondep_3195_);
v_kind_boxed_3205_ = lean_unbox(v_kind_3196_);
v_res_3206_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_3190_, v_name_3191_, v_type_3192_, v_val_3193_, v_k_3194_, v_nondep_boxed_3204_, v_kind_boxed_3205_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec(v___y_3197_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_3207_, lean_object* v_ref_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_3208_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_3215_, lean_object* v_ref_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_3215_, v_ref_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_3223_, lean_object* v_x_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_3233_, lean_object* v_x_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(v_00_u03b1_3233_, v_x_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec(v___y_3235_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_3243_, lean_object* v_m_3244_, lean_object* v_a_3245_, lean_object* v_b_3246_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_m_3244_, v_a_3245_, v_b_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_3248_, lean_object* v_a_3249_, lean_object* v_x_3250_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_3249_, v_x_3250_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_3252_, lean_object* v_a_3253_, lean_object* v_x_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_3252_, v_a_3253_, v_x_3254_);
lean_dec(v_x_3254_);
lean_dec_ref(v_a_3253_);
return v_res_3255_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_3256_, lean_object* v_a_3257_, lean_object* v_x_3258_){
_start:
{
uint8_t v___x_3259_; 
v___x_3259_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_3257_, v_x_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_3260_, lean_object* v_a_3261_, lean_object* v_x_3262_){
_start:
{
uint8_t v_res_3263_; lean_object* v_r_3264_; 
v_res_3263_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_3260_, v_a_3261_, v_x_3262_);
lean_dec(v_x_3262_);
lean_dec_ref(v_a_3261_);
v_r_3264_ = lean_box(v_res_3263_);
return v_r_3264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_3265_, lean_object* v_data_3266_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_data_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_3268_, lean_object* v_a_3269_, lean_object* v_b_3270_, lean_object* v_x_3271_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_3269_, v_b_3270_, v_x_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_3273_, lean_object* v_i_3274_, lean_object* v_source_3275_, lean_object* v_target_3276_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_3274_, v_source_3275_, v_target_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_3278_, lean_object* v_x_3279_, lean_object* v_x_3280_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_3279_, v_x_3280_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(lean_object* v_mvarId_3282_, lean_object* v_x_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3282_, v_x_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
v_a_3298_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3289_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3289_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(lean_object* v_mvarId_3306_, lean_object* v_x_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3306_, v_x_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_object* v_00_u03b1_3314_, lean_object* v_mvarId_3315_, lean_object* v_x_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
lean_object* v___x_3322_; 
v___x_3322_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3315_, v_x_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(lean_object* v_00_u03b1_3323_, lean_object* v_mvarId_3324_, lean_object* v_x_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(v_00_u03b1_3323_, v_mvarId_3324_, v_x_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(uint8_t v_elimTrivial_3332_, lean_object* v_as_3333_, size_t v_sz_3334_, size_t v_i_3335_, lean_object* v_b_3336_){
_start:
{
uint8_t v___x_3338_; 
v___x_3338_ = lean_usize_dec_lt(v_i_3335_, v_sz_3334_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3339_; 
v___x_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3339_, 0, v_b_3336_);
return v___x_3339_;
}
else
{
lean_object* v_snd_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3387_; 
v_snd_3340_ = lean_ctor_get(v_b_3336_, 1);
v_isSharedCheck_3387_ = !lean_is_exclusive(v_b_3336_);
if (v_isSharedCheck_3387_ == 0)
{
lean_object* v_unused_3388_; 
v_unused_3388_ = lean_ctor_get(v_b_3336_, 0);
lean_dec(v_unused_3388_);
v___x_3342_ = v_b_3336_;
v_isShared_3343_ = v_isSharedCheck_3387_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_snd_3340_);
lean_dec(v_b_3336_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3387_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3344_; lean_object* v_a_3346_; lean_object* v_a_3353_; 
v___x_3344_ = lean_box(0);
v_a_3353_ = lean_array_uget_borrowed(v_as_3333_, v_i_3335_);
if (lean_obj_tag(v_a_3353_) == 0)
{
v_a_3346_ = v_snd_3340_;
goto v___jp_3345_;
}
else
{
lean_object* v_val_3354_; lean_object* v_fst_3355_; lean_object* v_snd_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3386_; 
v_val_3354_ = lean_ctor_get(v_a_3353_, 0);
v_fst_3355_ = lean_ctor_get(v_snd_3340_, 0);
v_snd_3356_ = lean_ctor_get(v_snd_3340_, 1);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_snd_3340_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3358_ = v_snd_3340_;
v_isShared_3359_ = v_isSharedCheck_3386_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_snd_3356_);
lean_inc(v_fst_3355_);
lean_dec(v_snd_3340_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3386_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
uint8_t v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = 0;
v___x_3361_ = l_Lean_LocalDecl_value_x3f(v_val_3354_, v___x_3360_);
if (lean_obj_tag(v___x_3361_) == 1)
{
lean_object* v_val_3362_; lean_object* v___x_3363_; 
v_val_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_val_3362_);
lean_dec_ref_known(v___x_3361_, 1);
v___x_3363_ = l_Lean_LocalDecl_type(v_val_3354_);
if (lean_obj_tag(v___x_3363_) == 10)
{
lean_object* v_data_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; uint8_t v___x_3368_; uint8_t v___x_3369_; 
v_data_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_data_3364_);
lean_dec_ref_known(v___x_3363_, 2);
v___x_3365_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3366_ = lean_unsigned_to_nat(2u);
v___x_3367_ = l_Lean_KVMap_getNat(v_data_3364_, v___x_3365_, v___x_3366_);
lean_dec(v_data_3364_);
v___x_3368_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3367_);
lean_dec(v___x_3367_);
v___x_3369_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3368_, v_val_3362_, v_elimTrivial_3332_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3370_ = l_Lean_LocalDecl_fvarId(v_val_3354_);
v___x_3371_ = l_Lean_mkFVar(v___x_3370_);
v___x_3372_ = lean_array_push(v_fst_3355_, v___x_3371_);
v___x_3373_ = lean_array_push(v_snd_3356_, v_val_3362_);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 1, v___x_3373_);
lean_ctor_set(v___x_3358_, 0, v___x_3372_);
v___x_3375_ = v___x_3358_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3376_, 1, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
v_a_3346_ = v___x_3375_;
goto v___jp_3345_;
}
}
else
{
lean_object* v___x_3378_; 
lean_dec(v_val_3362_);
if (v_isShared_3359_ == 0)
{
v___x_3378_ = v___x_3358_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_fst_3355_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v_snd_3356_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
v_a_3346_ = v___x_3378_;
goto v___jp_3345_;
}
}
}
else
{
lean_object* v___x_3381_; 
lean_dec_ref(v___x_3363_);
lean_dec(v_val_3362_);
if (v_isShared_3359_ == 0)
{
v___x_3381_ = v___x_3358_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_fst_3355_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_snd_3356_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
v_a_3346_ = v___x_3381_;
goto v___jp_3345_;
}
}
}
else
{
lean_object* v___x_3384_; 
lean_dec(v___x_3361_);
if (v_isShared_3359_ == 0)
{
v___x_3384_ = v___x_3358_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_fst_3355_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_snd_3356_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
v_a_3346_ = v___x_3384_;
goto v___jp_3345_;
}
}
}
}
v___jp_3345_:
{
lean_object* v___x_3348_; 
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 1, v_a_3346_);
lean_ctor_set(v___x_3342_, 0, v___x_3344_);
v___x_3348_ = v___x_3342_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3344_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v_a_3346_);
v___x_3348_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
size_t v___x_3349_; size_t v___x_3350_; 
v___x_3349_ = ((size_t)1ULL);
v___x_3350_ = lean_usize_add(v_i_3335_, v___x_3349_);
v_i_3335_ = v___x_3350_;
v_b_3336_ = v___x_3348_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_elimTrivial_3389_, lean_object* v_as_3390_, lean_object* v_sz_3391_, lean_object* v_i_3392_, lean_object* v_b_3393_, lean_object* v___y_3394_){
_start:
{
uint8_t v_elimTrivial_boxed_3395_; size_t v_sz_boxed_3396_; size_t v_i_boxed_3397_; lean_object* v_res_3398_; 
v_elimTrivial_boxed_3395_ = lean_unbox(v_elimTrivial_3389_);
v_sz_boxed_3396_ = lean_unbox_usize(v_sz_3391_);
lean_dec(v_sz_3391_);
v_i_boxed_3397_ = lean_unbox_usize(v_i_3392_);
lean_dec(v_i_3392_);
v_res_3398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_boxed_3395_, v_as_3390_, v_sz_boxed_3396_, v_i_boxed_3397_, v_b_3393_);
lean_dec_ref(v_as_3390_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(uint8_t v_elimTrivial_3399_, lean_object* v_as_3400_, size_t v_sz_3401_, size_t v_i_3402_, lean_object* v_b_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
uint8_t v___x_3409_; 
v___x_3409_ = lean_usize_dec_lt(v_i_3402_, v_sz_3401_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; 
v___x_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3410_, 0, v_b_3403_);
return v___x_3410_;
}
else
{
lean_object* v_snd_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3458_; 
v_snd_3411_ = lean_ctor_get(v_b_3403_, 1);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_b_3403_);
if (v_isSharedCheck_3458_ == 0)
{
lean_object* v_unused_3459_; 
v_unused_3459_ = lean_ctor_get(v_b_3403_, 0);
lean_dec(v_unused_3459_);
v___x_3413_ = v_b_3403_;
v_isShared_3414_ = v_isSharedCheck_3458_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_snd_3411_);
lean_dec(v_b_3403_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3458_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; lean_object* v_a_3417_; lean_object* v_a_3424_; 
v___x_3415_ = lean_box(0);
v_a_3424_ = lean_array_uget_borrowed(v_as_3400_, v_i_3402_);
if (lean_obj_tag(v_a_3424_) == 0)
{
v_a_3417_ = v_snd_3411_;
goto v___jp_3416_;
}
else
{
lean_object* v_val_3425_; lean_object* v_fst_3426_; lean_object* v_snd_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3457_; 
v_val_3425_ = lean_ctor_get(v_a_3424_, 0);
v_fst_3426_ = lean_ctor_get(v_snd_3411_, 0);
v_snd_3427_ = lean_ctor_get(v_snd_3411_, 1);
v_isSharedCheck_3457_ = !lean_is_exclusive(v_snd_3411_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3429_ = v_snd_3411_;
v_isShared_3430_ = v_isSharedCheck_3457_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_snd_3427_);
lean_inc(v_fst_3426_);
lean_dec(v_snd_3411_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3457_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
uint8_t v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = 0;
v___x_3432_ = l_Lean_LocalDecl_value_x3f(v_val_3425_, v___x_3431_);
if (lean_obj_tag(v___x_3432_) == 1)
{
lean_object* v_val_3433_; lean_object* v___x_3434_; 
v_val_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_val_3433_);
lean_dec_ref_known(v___x_3432_, 1);
v___x_3434_ = l_Lean_LocalDecl_type(v_val_3425_);
if (lean_obj_tag(v___x_3434_) == 10)
{
lean_object* v_data_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; uint8_t v___x_3440_; 
v_data_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_data_3435_);
lean_dec_ref_known(v___x_3434_, 2);
v___x_3436_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3437_ = lean_unsigned_to_nat(2u);
v___x_3438_ = l_Lean_KVMap_getNat(v_data_3435_, v___x_3436_, v___x_3437_);
lean_dec(v_data_3435_);
v___x_3439_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3438_);
lean_dec(v___x_3438_);
v___x_3440_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3439_, v_val_3433_, v_elimTrivial_3399_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3446_; 
v___x_3441_ = l_Lean_LocalDecl_fvarId(v_val_3425_);
v___x_3442_ = l_Lean_mkFVar(v___x_3441_);
v___x_3443_ = lean_array_push(v_fst_3426_, v___x_3442_);
v___x_3444_ = lean_array_push(v_snd_3427_, v_val_3433_);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 1, v___x_3444_);
lean_ctor_set(v___x_3429_, 0, v___x_3443_);
v___x_3446_ = v___x_3429_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3443_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
v_a_3417_ = v___x_3446_;
goto v___jp_3416_;
}
}
else
{
lean_object* v___x_3449_; 
lean_dec(v_val_3433_);
if (v_isShared_3430_ == 0)
{
v___x_3449_ = v___x_3429_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_fst_3426_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_snd_3427_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
v_a_3417_ = v___x_3449_;
goto v___jp_3416_;
}
}
}
else
{
lean_object* v___x_3452_; 
lean_dec_ref(v___x_3434_);
lean_dec(v_val_3433_);
if (v_isShared_3430_ == 0)
{
v___x_3452_ = v___x_3429_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_fst_3426_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_snd_3427_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
v_a_3417_ = v___x_3452_;
goto v___jp_3416_;
}
}
}
else
{
lean_object* v___x_3455_; 
lean_dec(v___x_3432_);
if (v_isShared_3430_ == 0)
{
v___x_3455_ = v___x_3429_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_fst_3426_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v_snd_3427_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
v_a_3417_ = v___x_3455_;
goto v___jp_3416_;
}
}
}
}
v___jp_3416_:
{
lean_object* v___x_3419_; 
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 1, v_a_3417_);
lean_ctor_set(v___x_3413_, 0, v___x_3415_);
v___x_3419_ = v___x_3413_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_a_3417_);
v___x_3419_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
size_t v___x_3420_; size_t v___x_3421_; lean_object* v___x_3422_; 
v___x_3420_ = ((size_t)1ULL);
v___x_3421_ = lean_usize_add(v_i_3402_, v___x_3420_);
v___x_3422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_3399_, v_as_3400_, v_sz_3401_, v___x_3421_, v___x_3419_);
return v___x_3422_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(lean_object* v_elimTrivial_3460_, lean_object* v_as_3461_, lean_object* v_sz_3462_, lean_object* v_i_3463_, lean_object* v_b_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
uint8_t v_elimTrivial_boxed_3470_; size_t v_sz_boxed_3471_; size_t v_i_boxed_3472_; lean_object* v_res_3473_; 
v_elimTrivial_boxed_3470_ = lean_unbox(v_elimTrivial_3460_);
v_sz_boxed_3471_ = lean_unbox_usize(v_sz_3462_);
lean_dec(v_sz_3462_);
v_i_boxed_3472_ = lean_unbox_usize(v_i_3463_);
lean_dec(v_i_3463_);
v_res_3473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_boxed_3470_, v_as_3461_, v_sz_boxed_3471_, v_i_boxed_3472_, v_b_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec_ref(v_as_3461_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(uint8_t v_elimTrivial_3474_, lean_object* v_as_3475_, size_t v_sz_3476_, size_t v_i_3477_, lean_object* v_b_3478_){
_start:
{
uint8_t v___x_3480_; 
v___x_3480_ = lean_usize_dec_lt(v_i_3477_, v_sz_3476_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; 
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v_b_3478_);
return v___x_3481_;
}
else
{
lean_object* v_snd_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3529_; 
v_snd_3482_ = lean_ctor_get(v_b_3478_, 1);
v_isSharedCheck_3529_ = !lean_is_exclusive(v_b_3478_);
if (v_isSharedCheck_3529_ == 0)
{
lean_object* v_unused_3530_; 
v_unused_3530_ = lean_ctor_get(v_b_3478_, 0);
lean_dec(v_unused_3530_);
v___x_3484_ = v_b_3478_;
v_isShared_3485_ = v_isSharedCheck_3529_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_snd_3482_);
lean_dec(v_b_3478_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3529_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3486_; lean_object* v_a_3488_; lean_object* v_a_3495_; 
v___x_3486_ = lean_box(0);
v_a_3495_ = lean_array_uget_borrowed(v_as_3475_, v_i_3477_);
if (lean_obj_tag(v_a_3495_) == 0)
{
v_a_3488_ = v_snd_3482_;
goto v___jp_3487_;
}
else
{
lean_object* v_val_3496_; lean_object* v_fst_3497_; lean_object* v_snd_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3528_; 
v_val_3496_ = lean_ctor_get(v_a_3495_, 0);
v_fst_3497_ = lean_ctor_get(v_snd_3482_, 0);
v_snd_3498_ = lean_ctor_get(v_snd_3482_, 1);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_snd_3482_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3500_ = v_snd_3482_;
v_isShared_3501_ = v_isSharedCheck_3528_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_snd_3498_);
lean_inc(v_fst_3497_);
lean_dec(v_snd_3482_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3528_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
uint8_t v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = 0;
v___x_3503_ = l_Lean_LocalDecl_value_x3f(v_val_3496_, v___x_3502_);
if (lean_obj_tag(v___x_3503_) == 1)
{
lean_object* v_val_3504_; lean_object* v___x_3505_; 
v_val_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_val_3504_);
lean_dec_ref_known(v___x_3503_, 1);
v___x_3505_ = l_Lean_LocalDecl_type(v_val_3496_);
if (lean_obj_tag(v___x_3505_) == 10)
{
lean_object* v_data_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; uint8_t v___x_3510_; uint8_t v___x_3511_; 
v_data_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_data_3506_);
lean_dec_ref_known(v___x_3505_, 2);
v___x_3507_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3508_ = lean_unsigned_to_nat(2u);
v___x_3509_ = l_Lean_KVMap_getNat(v_data_3506_, v___x_3507_, v___x_3508_);
lean_dec(v_data_3506_);
v___x_3510_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3509_);
lean_dec(v___x_3509_);
v___x_3511_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3510_, v_val_3504_, v_elimTrivial_3474_);
if (v___x_3511_ == 0)
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3517_; 
v___x_3512_ = l_Lean_LocalDecl_fvarId(v_val_3496_);
v___x_3513_ = l_Lean_mkFVar(v___x_3512_);
v___x_3514_ = lean_array_push(v_fst_3497_, v___x_3513_);
v___x_3515_ = lean_array_push(v_snd_3498_, v_val_3504_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v___x_3515_);
lean_ctor_set(v___x_3500_, 0, v___x_3514_);
v___x_3517_ = v___x_3500_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3514_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
v_a_3488_ = v___x_3517_;
goto v___jp_3487_;
}
}
else
{
lean_object* v___x_3520_; 
lean_dec(v_val_3504_);
if (v_isShared_3501_ == 0)
{
v___x_3520_ = v___x_3500_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_fst_3497_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_snd_3498_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
v_a_3488_ = v___x_3520_;
goto v___jp_3487_;
}
}
}
else
{
lean_object* v___x_3523_; 
lean_dec_ref(v___x_3505_);
lean_dec(v_val_3504_);
if (v_isShared_3501_ == 0)
{
v___x_3523_ = v___x_3500_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_fst_3497_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v_snd_3498_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
v_a_3488_ = v___x_3523_;
goto v___jp_3487_;
}
}
}
else
{
lean_object* v___x_3526_; 
lean_dec(v___x_3503_);
if (v_isShared_3501_ == 0)
{
v___x_3526_ = v___x_3500_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_fst_3497_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_snd_3498_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
v_a_3488_ = v___x_3526_;
goto v___jp_3487_;
}
}
}
}
v___jp_3487_:
{
lean_object* v___x_3490_; 
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 1, v_a_3488_);
lean_ctor_set(v___x_3484_, 0, v___x_3486_);
v___x_3490_ = v___x_3484_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_a_3488_);
v___x_3490_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
size_t v___x_3491_; size_t v___x_3492_; 
v___x_3491_ = ((size_t)1ULL);
v___x_3492_ = lean_usize_add(v_i_3477_, v___x_3491_);
v_i_3477_ = v___x_3492_;
v_b_3478_ = v___x_3490_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_elimTrivial_3531_, lean_object* v_as_3532_, lean_object* v_sz_3533_, lean_object* v_i_3534_, lean_object* v_b_3535_, lean_object* v___y_3536_){
_start:
{
uint8_t v_elimTrivial_boxed_3537_; size_t v_sz_boxed_3538_; size_t v_i_boxed_3539_; lean_object* v_res_3540_; 
v_elimTrivial_boxed_3537_ = lean_unbox(v_elimTrivial_3531_);
v_sz_boxed_3538_ = lean_unbox_usize(v_sz_3533_);
lean_dec(v_sz_3533_);
v_i_boxed_3539_ = lean_unbox_usize(v_i_3534_);
lean_dec(v_i_3534_);
v_res_3540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_boxed_3537_, v_as_3532_, v_sz_boxed_3538_, v_i_boxed_3539_, v_b_3535_);
lean_dec_ref(v_as_3532_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(uint8_t v_elimTrivial_3541_, lean_object* v_as_3542_, size_t v_sz_3543_, size_t v_i_3544_, lean_object* v_b_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
uint8_t v___x_3551_; 
v___x_3551_ = lean_usize_dec_lt(v_i_3544_, v_sz_3543_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; 
v___x_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3552_, 0, v_b_3545_);
return v___x_3552_;
}
else
{
lean_object* v_snd_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3600_; 
v_snd_3553_ = lean_ctor_get(v_b_3545_, 1);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_b_3545_);
if (v_isSharedCheck_3600_ == 0)
{
lean_object* v_unused_3601_; 
v_unused_3601_ = lean_ctor_get(v_b_3545_, 0);
lean_dec(v_unused_3601_);
v___x_3555_ = v_b_3545_;
v_isShared_3556_ = v_isSharedCheck_3600_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_snd_3553_);
lean_dec(v_b_3545_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3600_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3557_; lean_object* v_a_3559_; lean_object* v_a_3566_; 
v___x_3557_ = lean_box(0);
v_a_3566_ = lean_array_uget_borrowed(v_as_3542_, v_i_3544_);
if (lean_obj_tag(v_a_3566_) == 0)
{
v_a_3559_ = v_snd_3553_;
goto v___jp_3558_;
}
else
{
lean_object* v_val_3567_; lean_object* v_fst_3568_; lean_object* v_snd_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3599_; 
v_val_3567_ = lean_ctor_get(v_a_3566_, 0);
v_fst_3568_ = lean_ctor_get(v_snd_3553_, 0);
v_snd_3569_ = lean_ctor_get(v_snd_3553_, 1);
v_isSharedCheck_3599_ = !lean_is_exclusive(v_snd_3553_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3571_ = v_snd_3553_;
v_isShared_3572_ = v_isSharedCheck_3599_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_snd_3569_);
lean_inc(v_fst_3568_);
lean_dec(v_snd_3553_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3599_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
uint8_t v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = 0;
v___x_3574_ = l_Lean_LocalDecl_value_x3f(v_val_3567_, v___x_3573_);
if (lean_obj_tag(v___x_3574_) == 1)
{
lean_object* v_val_3575_; lean_object* v___x_3576_; 
v_val_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_val_3575_);
lean_dec_ref_known(v___x_3574_, 1);
v___x_3576_ = l_Lean_LocalDecl_type(v_val_3567_);
if (lean_obj_tag(v___x_3576_) == 10)
{
lean_object* v_data_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; uint8_t v___x_3581_; uint8_t v___x_3582_; 
v_data_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_data_3577_);
lean_dec_ref_known(v___x_3576_, 2);
v___x_3578_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2));
v___x_3579_ = lean_unsigned_to_nat(2u);
v___x_3580_ = l_Lean_KVMap_getNat(v_data_3577_, v___x_3578_, v___x_3579_);
lean_dec(v_data_3577_);
v___x_3581_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3580_);
lean_dec(v___x_3580_);
v___x_3582_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3581_, v_val_3575_, v_elimTrivial_3541_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3588_; 
v___x_3583_ = l_Lean_LocalDecl_fvarId(v_val_3567_);
v___x_3584_ = l_Lean_mkFVar(v___x_3583_);
v___x_3585_ = lean_array_push(v_fst_3568_, v___x_3584_);
v___x_3586_ = lean_array_push(v_snd_3569_, v_val_3575_);
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 1, v___x_3586_);
lean_ctor_set(v___x_3571_, 0, v___x_3585_);
v___x_3588_ = v___x_3571_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3585_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v___x_3586_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
v_a_3559_ = v___x_3588_;
goto v___jp_3558_;
}
}
else
{
lean_object* v___x_3591_; 
lean_dec(v_val_3575_);
if (v_isShared_3572_ == 0)
{
v___x_3591_ = v___x_3571_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_fst_3568_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v_snd_3569_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
v_a_3559_ = v___x_3591_;
goto v___jp_3558_;
}
}
}
else
{
lean_object* v___x_3594_; 
lean_dec_ref(v___x_3576_);
lean_dec(v_val_3575_);
if (v_isShared_3572_ == 0)
{
v___x_3594_ = v___x_3571_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_fst_3568_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_snd_3569_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
v_a_3559_ = v___x_3594_;
goto v___jp_3558_;
}
}
}
else
{
lean_object* v___x_3597_; 
lean_dec(v___x_3574_);
if (v_isShared_3572_ == 0)
{
v___x_3597_ = v___x_3571_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_fst_3568_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_snd_3569_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
v_a_3559_ = v___x_3597_;
goto v___jp_3558_;
}
}
}
}
v___jp_3558_:
{
lean_object* v___x_3561_; 
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 1, v_a_3559_);
lean_ctor_set(v___x_3555_, 0, v___x_3557_);
v___x_3561_ = v___x_3555_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3557_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_a_3559_);
v___x_3561_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
size_t v___x_3562_; size_t v___x_3563_; lean_object* v___x_3564_; 
v___x_3562_ = ((size_t)1ULL);
v___x_3563_ = lean_usize_add(v_i_3544_, v___x_3562_);
v___x_3564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_3541_, v_as_3542_, v_sz_3543_, v___x_3563_, v___x_3561_);
return v___x_3564_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(lean_object* v_elimTrivial_3602_, lean_object* v_as_3603_, lean_object* v_sz_3604_, lean_object* v_i_3605_, lean_object* v_b_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
uint8_t v_elimTrivial_boxed_3612_; size_t v_sz_boxed_3613_; size_t v_i_boxed_3614_; lean_object* v_res_3615_; 
v_elimTrivial_boxed_3612_ = lean_unbox(v_elimTrivial_3602_);
v_sz_boxed_3613_ = lean_unbox_usize(v_sz_3604_);
lean_dec(v_sz_3604_);
v_i_boxed_3614_ = lean_unbox_usize(v_i_3605_);
lean_dec(v_i_3605_);
v_res_3615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_boxed_3612_, v_as_3603_, v_sz_boxed_3613_, v_i_boxed_3614_, v_b_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec_ref(v_as_3603_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(lean_object* v_init_3616_, uint8_t v_elimTrivial_3617_, lean_object* v_n_3618_, lean_object* v_b_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
if (lean_obj_tag(v_n_3618_) == 0)
{
lean_object* v_cs_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; size_t v_sz_3628_; size_t v___x_3629_; lean_object* v___x_3630_; 
v_cs_3625_ = lean_ctor_get(v_n_3618_, 0);
v___x_3626_ = lean_box(0);
v___x_3627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3626_);
lean_ctor_set(v___x_3627_, 1, v_b_3619_);
v_sz_3628_ = lean_array_size(v_cs_3625_);
v___x_3629_ = ((size_t)0ULL);
v___x_3630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3616_, v_elimTrivial_3617_, v_cs_3625_, v_sz_3628_, v___x_3629_, v___x_3627_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3645_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3633_ = v___x_3630_;
v_isShared_3634_ = v_isSharedCheck_3645_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3630_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3645_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v_fst_3635_; 
v_fst_3635_ = lean_ctor_get(v_a_3631_, 0);
if (lean_obj_tag(v_fst_3635_) == 0)
{
lean_object* v_snd_3636_; lean_object* v___x_3637_; lean_object* v___x_3639_; 
v_snd_3636_ = lean_ctor_get(v_a_3631_, 1);
lean_inc(v_snd_3636_);
lean_dec(v_a_3631_);
v___x_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3637_, 0, v_snd_3636_);
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 0, v___x_3637_);
v___x_3639_ = v___x_3633_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3637_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
else
{
lean_object* v_val_3641_; lean_object* v___x_3643_; 
lean_inc_ref(v_fst_3635_);
lean_dec(v_a_3631_);
v_val_3641_ = lean_ctor_get(v_fst_3635_, 0);
lean_inc(v_val_3641_);
lean_dec_ref_known(v_fst_3635_, 1);
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 0, v_val_3641_);
v___x_3643_ = v___x_3633_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_val_3641_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
v_a_3646_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3630_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3630_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
else
{
lean_object* v_vs_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; size_t v_sz_3657_; size_t v___x_3658_; lean_object* v___x_3659_; 
v_vs_3654_ = lean_ctor_get(v_n_3618_, 0);
v___x_3655_ = lean_box(0);
v___x_3656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3655_);
lean_ctor_set(v___x_3656_, 1, v_b_3619_);
v_sz_3657_ = lean_array_size(v_vs_3654_);
v___x_3658_ = ((size_t)0ULL);
v___x_3659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_3617_, v_vs_3654_, v_sz_3657_, v___x_3658_, v___x_3656_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3674_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3662_ = v___x_3659_;
v_isShared_3663_ = v_isSharedCheck_3674_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3659_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3674_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v_fst_3664_; 
v_fst_3664_ = lean_ctor_get(v_a_3660_, 0);
if (lean_obj_tag(v_fst_3664_) == 0)
{
lean_object* v_snd_3665_; lean_object* v___x_3666_; lean_object* v___x_3668_; 
v_snd_3665_ = lean_ctor_get(v_a_3660_, 1);
lean_inc(v_snd_3665_);
lean_dec(v_a_3660_);
v___x_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3666_, 0, v_snd_3665_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 0, v___x_3666_);
v___x_3668_ = v___x_3662_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3666_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
else
{
lean_object* v_val_3670_; lean_object* v___x_3672_; 
lean_inc_ref(v_fst_3664_);
lean_dec(v_a_3660_);
v_val_3670_ = lean_ctor_get(v_fst_3664_, 0);
lean_inc(v_val_3670_);
lean_dec_ref_known(v_fst_3664_, 1);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 0, v_val_3670_);
v___x_3672_ = v___x_3662_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_val_3670_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
v_a_3675_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3659_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3659_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(lean_object* v_init_3683_, uint8_t v_elimTrivial_3684_, lean_object* v_as_3685_, size_t v_sz_3686_, size_t v_i_3687_, lean_object* v_b_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
uint8_t v___x_3694_; 
v___x_3694_ = lean_usize_dec_lt(v_i_3687_, v_sz_3686_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3695_; 
v___x_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3695_, 0, v_b_3688_);
return v___x_3695_;
}
else
{
lean_object* v_snd_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3730_; 
v_snd_3696_ = lean_ctor_get(v_b_3688_, 1);
v_isSharedCheck_3730_ = !lean_is_exclusive(v_b_3688_);
if (v_isSharedCheck_3730_ == 0)
{
lean_object* v_unused_3731_; 
v_unused_3731_ = lean_ctor_get(v_b_3688_, 0);
lean_dec(v_unused_3731_);
v___x_3698_ = v_b_3688_;
v_isShared_3699_ = v_isSharedCheck_3730_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_snd_3696_);
lean_dec(v_b_3688_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3730_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3700_; lean_object* v_a_3701_; lean_object* v___x_3702_; 
v___x_3700_ = lean_box(0);
v_a_3701_ = lean_array_uget_borrowed(v_as_3685_, v_i_3687_);
lean_inc(v_snd_3696_);
v___x_3702_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3683_, v_elimTrivial_3684_, v_a_3701_, v_snd_3696_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3721_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3705_ = v___x_3702_;
v_isShared_3706_ = v_isSharedCheck_3721_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3702_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3721_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
if (lean_obj_tag(v_a_3703_) == 0)
{
lean_object* v___x_3707_; lean_object* v___x_3709_; 
v___x_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3707_, 0, v_a_3703_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v___x_3707_);
v___x_3709_ = v___x_3698_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3707_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_snd_3696_);
v___x_3709_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
lean_object* v___x_3711_; 
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 0, v___x_3709_);
v___x_3711_ = v___x_3705_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3709_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3716_; 
lean_del_object(v___x_3705_);
lean_dec(v_snd_3696_);
v_a_3714_ = lean_ctor_get(v_a_3703_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v_a_3703_, 1);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 1, v_a_3714_);
lean_ctor_set(v___x_3698_, 0, v___x_3700_);
v___x_3716_ = v___x_3698_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3700_);
lean_ctor_set(v_reuseFailAlloc_3720_, 1, v_a_3714_);
v___x_3716_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
size_t v___x_3717_; size_t v___x_3718_; 
v___x_3717_ = ((size_t)1ULL);
v___x_3718_ = lean_usize_add(v_i_3687_, v___x_3717_);
v_i_3687_ = v___x_3718_;
v_b_3688_ = v___x_3716_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_del_object(v___x_3698_);
lean_dec(v_snd_3696_);
v_a_3722_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3702_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3702_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(lean_object* v_init_3732_, lean_object* v_elimTrivial_3733_, lean_object* v_as_3734_, lean_object* v_sz_3735_, lean_object* v_i_3736_, lean_object* v_b_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
uint8_t v_elimTrivial_boxed_3743_; size_t v_sz_boxed_3744_; size_t v_i_boxed_3745_; lean_object* v_res_3746_; 
v_elimTrivial_boxed_3743_ = lean_unbox(v_elimTrivial_3733_);
v_sz_boxed_3744_ = lean_unbox_usize(v_sz_3735_);
lean_dec(v_sz_3735_);
v_i_boxed_3745_ = lean_unbox_usize(v_i_3736_);
lean_dec(v_i_3736_);
v_res_3746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3732_, v_elimTrivial_boxed_3743_, v_as_3734_, v_sz_boxed_3744_, v_i_boxed_3745_, v_b_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec_ref(v_as_3734_);
lean_dec_ref(v_init_3732_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(lean_object* v_init_3747_, lean_object* v_elimTrivial_3748_, lean_object* v_n_3749_, lean_object* v_b_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
uint8_t v_elimTrivial_boxed_3756_; lean_object* v_res_3757_; 
v_elimTrivial_boxed_3756_ = lean_unbox(v_elimTrivial_3748_);
v_res_3757_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3747_, v_elimTrivial_boxed_3756_, v_n_3749_, v_b_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec_ref(v_n_3749_);
lean_dec_ref(v_init_3747_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(uint8_t v_elimTrivial_3758_, lean_object* v_t_3759_, lean_object* v_init_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_root_3766_; lean_object* v_tail_3767_; lean_object* v___x_3768_; 
v_root_3766_ = lean_ctor_get(v_t_3759_, 0);
v_tail_3767_ = lean_ctor_get(v_t_3759_, 1);
lean_inc_ref(v_init_3760_);
v___x_3768_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3760_, v_elimTrivial_3758_, v_root_3766_, v_init_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
lean_dec_ref(v_init_3760_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3805_; 
v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3771_ = v___x_3768_;
v_isShared_3772_ = v_isSharedCheck_3805_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3768_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3805_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
if (lean_obj_tag(v_a_3769_) == 0)
{
lean_object* v_a_3773_; lean_object* v___x_3775_; 
v_a_3773_ = lean_ctor_get(v_a_3769_, 0);
lean_inc(v_a_3773_);
lean_dec_ref_known(v_a_3769_, 1);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 0, v_a_3773_);
v___x_3775_ = v___x_3771_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3773_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; size_t v_sz_3780_; size_t v___x_3781_; lean_object* v___x_3782_; 
lean_del_object(v___x_3771_);
v_a_3777_ = lean_ctor_get(v_a_3769_, 0);
lean_inc(v_a_3777_);
lean_dec_ref_known(v_a_3769_, 1);
v___x_3778_ = lean_box(0);
v___x_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3778_);
lean_ctor_set(v___x_3779_, 1, v_a_3777_);
v_sz_3780_ = lean_array_size(v_tail_3767_);
v___x_3781_ = ((size_t)0ULL);
v___x_3782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_3758_, v_tail_3767_, v_sz_3780_, v___x_3781_, v___x_3779_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3796_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3785_ = v___x_3782_;
v_isShared_3786_ = v_isSharedCheck_3796_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3782_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3796_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v_fst_3787_; 
v_fst_3787_ = lean_ctor_get(v_a_3783_, 0);
if (lean_obj_tag(v_fst_3787_) == 0)
{
lean_object* v_snd_3788_; lean_object* v___x_3790_; 
v_snd_3788_ = lean_ctor_get(v_a_3783_, 1);
lean_inc(v_snd_3788_);
lean_dec(v_a_3783_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v_snd_3788_);
v___x_3790_ = v___x_3785_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_snd_3788_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
else
{
lean_object* v_val_3792_; lean_object* v___x_3794_; 
lean_inc_ref(v_fst_3787_);
lean_dec(v_a_3783_);
v_val_3792_ = lean_ctor_get(v_fst_3787_, 0);
lean_inc(v_val_3792_);
lean_dec_ref_known(v_fst_3787_, 1);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v_val_3792_);
v___x_3794_ = v___x_3785_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_val_3792_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
v_a_3797_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3782_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3782_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
v_a_3806_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3768_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3768_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(lean_object* v_elimTrivial_3814_, lean_object* v_t_3815_, lean_object* v_init_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
uint8_t v_elimTrivial_boxed_3822_; lean_object* v_res_3823_; 
v_elimTrivial_boxed_3822_ = lean_unbox(v_elimTrivial_3814_);
v_res_3823_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_boxed_3822_, v_t_3815_, v_init_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec_ref(v_t_3815_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(lean_object* v_as_3824_, size_t v_sz_3825_, size_t v_i_3826_, lean_object* v_b_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
uint8_t v___x_3833_; 
v___x_3833_ = lean_usize_dec_lt(v_i_3826_, v_sz_3825_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3834_; 
v___x_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3834_, 0, v_b_3827_);
return v___x_3834_;
}
else
{
lean_object* v_a_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
v_a_3835_ = lean_array_uget_borrowed(v_as_3824_, v_i_3826_);
v___x_3836_ = l_Lean_Expr_fvarId_x21(v_a_3835_);
v___x_3837_ = l_Lean_MVarId_tryClear(v_b_3827_, v___x_3836_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; size_t v___x_3839_; size_t v___x_3840_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_a_3838_);
lean_dec_ref_known(v___x_3837_, 1);
v___x_3839_ = ((size_t)1ULL);
v___x_3840_ = lean_usize_add(v_i_3826_, v___x_3839_);
v_i_3826_ = v___x_3840_;
v_b_3827_ = v_a_3838_;
goto _start;
}
else
{
return v___x_3837_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(lean_object* v_as_3842_, lean_object* v_sz_3843_, lean_object* v_i_3844_, lean_object* v_b_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
size_t v_sz_boxed_3851_; size_t v_i_boxed_3852_; lean_object* v_res_3853_; 
v_sz_boxed_3851_ = lean_unbox_usize(v_sz_3843_);
lean_dec(v_sz_3843_);
v_i_boxed_3852_ = lean_unbox_usize(v_i_3844_);
lean_dec(v_i_3844_);
v_res_3853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_as_3842_, v_sz_boxed_3851_, v_i_boxed_3852_, v_b_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec_ref(v_as_3842_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(lean_object* v_x_3854_, lean_object* v_x_3855_, lean_object* v_x_3856_, lean_object* v_x_3857_){
_start:
{
lean_object* v_ks_3858_; lean_object* v_vs_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3883_; 
v_ks_3858_ = lean_ctor_get(v_x_3854_, 0);
v_vs_3859_ = lean_ctor_get(v_x_3854_, 1);
v_isSharedCheck_3883_ = !lean_is_exclusive(v_x_3854_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3861_ = v_x_3854_;
v_isShared_3862_ = v_isSharedCheck_3883_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_vs_3859_);
lean_inc(v_ks_3858_);
lean_dec(v_x_3854_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3883_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3863_; uint8_t v___x_3864_; 
v___x_3863_ = lean_array_get_size(v_ks_3858_);
v___x_3864_ = lean_nat_dec_lt(v_x_3855_, v___x_3863_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3868_; 
lean_dec(v_x_3855_);
v___x_3865_ = lean_array_push(v_ks_3858_, v_x_3856_);
v___x_3866_ = lean_array_push(v_vs_3859_, v_x_3857_);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 1, v___x_3866_);
lean_ctor_set(v___x_3861_, 0, v___x_3865_);
v___x_3868_ = v___x_3861_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3865_);
lean_ctor_set(v_reuseFailAlloc_3869_, 1, v___x_3866_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
else
{
lean_object* v_k_x27_3870_; uint8_t v___x_3871_; 
v_k_x27_3870_ = lean_array_fget_borrowed(v_ks_3858_, v_x_3855_);
v___x_3871_ = l_Lean_instBEqMVarId_beq(v_x_3856_, v_k_x27_3870_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3873_; 
if (v_isShared_3862_ == 0)
{
v___x_3873_ = v___x_3861_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_ks_3858_);
lean_ctor_set(v_reuseFailAlloc_3877_, 1, v_vs_3859_);
v___x_3873_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3874_ = lean_unsigned_to_nat(1u);
v___x_3875_ = lean_nat_add(v_x_3855_, v___x_3874_);
lean_dec(v_x_3855_);
v_x_3854_ = v___x_3873_;
v_x_3855_ = v___x_3875_;
goto _start;
}
}
else
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3881_; 
v___x_3878_ = lean_array_fset(v_ks_3858_, v_x_3855_, v_x_3856_);
v___x_3879_ = lean_array_fset(v_vs_3859_, v_x_3855_, v_x_3857_);
lean_dec(v_x_3855_);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 1, v___x_3879_);
lean_ctor_set(v___x_3861_, 0, v___x_3878_);
v___x_3881_ = v___x_3861_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3878_);
lean_ctor_set(v_reuseFailAlloc_3882_, 1, v___x_3879_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(lean_object* v_n_3884_, lean_object* v_k_3885_, lean_object* v_v_3886_){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = lean_unsigned_to_nat(0u);
v___x_3888_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_n_3884_, v___x_3887_, v_k_3885_, v_v_3886_);
return v___x_3888_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(lean_object* v_x_3890_, size_t v_x_3891_, size_t v_x_3892_, lean_object* v_x_3893_, lean_object* v_x_3894_){
_start:
{
if (lean_obj_tag(v_x_3890_) == 0)
{
lean_object* v_es_3895_; size_t v___x_3896_; size_t v___x_3897_; lean_object* v_j_3898_; lean_object* v___x_3899_; uint8_t v___x_3900_; 
v_es_3895_ = lean_ctor_get(v_x_3890_, 0);
v___x_3896_ = ((size_t)31ULL);
v___x_3897_ = lean_usize_land(v_x_3891_, v___x_3896_);
v_j_3898_ = lean_usize_to_nat(v___x_3897_);
v___x_3899_ = lean_array_get_size(v_es_3895_);
v___x_3900_ = lean_nat_dec_lt(v_j_3898_, v___x_3899_);
if (v___x_3900_ == 0)
{
lean_dec(v_j_3898_);
lean_dec(v_x_3894_);
lean_dec(v_x_3893_);
return v_x_3890_;
}
else
{
lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3939_; 
lean_inc_ref(v_es_3895_);
v_isSharedCheck_3939_ = !lean_is_exclusive(v_x_3890_);
if (v_isSharedCheck_3939_ == 0)
{
lean_object* v_unused_3940_; 
v_unused_3940_ = lean_ctor_get(v_x_3890_, 0);
lean_dec(v_unused_3940_);
v___x_3902_ = v_x_3890_;
v_isShared_3903_ = v_isSharedCheck_3939_;
goto v_resetjp_3901_;
}
else
{
lean_dec(v_x_3890_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3939_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v_v_3904_; lean_object* v___x_3905_; lean_object* v_xs_x27_3906_; lean_object* v___y_3908_; 
v_v_3904_ = lean_array_fget(v_es_3895_, v_j_3898_);
v___x_3905_ = lean_box(0);
v_xs_x27_3906_ = lean_array_fset(v_es_3895_, v_j_3898_, v___x_3905_);
switch(lean_obj_tag(v_v_3904_))
{
case 0:
{
lean_object* v_key_3913_; lean_object* v_val_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3924_; 
v_key_3913_ = lean_ctor_get(v_v_3904_, 0);
v_val_3914_ = lean_ctor_get(v_v_3904_, 1);
v_isSharedCheck_3924_ = !lean_is_exclusive(v_v_3904_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3916_ = v_v_3904_;
v_isShared_3917_ = v_isSharedCheck_3924_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_val_3914_);
lean_inc(v_key_3913_);
lean_dec(v_v_3904_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3924_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
uint8_t v___x_3918_; 
v___x_3918_ = l_Lean_instBEqMVarId_beq(v_x_3893_, v_key_3913_);
if (v___x_3918_ == 0)
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
lean_del_object(v___x_3916_);
v___x_3919_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3913_, v_val_3914_, v_x_3893_, v_x_3894_);
v___x_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3919_);
v___y_3908_ = v___x_3920_;
goto v___jp_3907_;
}
else
{
lean_object* v___x_3922_; 
lean_dec(v_val_3914_);
lean_dec(v_key_3913_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 1, v_x_3894_);
lean_ctor_set(v___x_3916_, 0, v_x_3893_);
v___x_3922_ = v___x_3916_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_x_3893_);
lean_ctor_set(v_reuseFailAlloc_3923_, 1, v_x_3894_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
v___y_3908_ = v___x_3922_;
goto v___jp_3907_;
}
}
}
}
case 1:
{
lean_object* v_node_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3937_; 
v_node_3925_ = lean_ctor_get(v_v_3904_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_v_3904_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3927_ = v_v_3904_;
v_isShared_3928_ = v_isSharedCheck_3937_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_node_3925_);
lean_dec(v_v_3904_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3937_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
size_t v___x_3929_; size_t v___x_3930_; size_t v___x_3931_; size_t v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3935_; 
v___x_3929_ = ((size_t)5ULL);
v___x_3930_ = lean_usize_shift_right(v_x_3891_, v___x_3929_);
v___x_3931_ = ((size_t)1ULL);
v___x_3932_ = lean_usize_add(v_x_3892_, v___x_3931_);
v___x_3933_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_node_3925_, v___x_3930_, v___x_3932_, v_x_3893_, v_x_3894_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 0, v___x_3933_);
v___x_3935_ = v___x_3927_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3933_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
v___y_3908_ = v___x_3935_;
goto v___jp_3907_;
}
}
}
default: 
{
lean_object* v___x_3938_; 
v___x_3938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3938_, 0, v_x_3893_);
lean_ctor_set(v___x_3938_, 1, v_x_3894_);
v___y_3908_ = v___x_3938_;
goto v___jp_3907_;
}
}
v___jp_3907_:
{
lean_object* v___x_3909_; lean_object* v___x_3911_; 
v___x_3909_ = lean_array_fset(v_xs_x27_3906_, v_j_3898_, v___y_3908_);
lean_dec(v_j_3898_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 0, v___x_3909_);
v___x_3911_ = v___x_3902_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3909_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
}
else
{
lean_object* v_ks_3941_; lean_object* v_vs_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3960_; 
v_ks_3941_ = lean_ctor_get(v_x_3890_, 0);
v_vs_3942_ = lean_ctor_get(v_x_3890_, 1);
v_isSharedCheck_3960_ = !lean_is_exclusive(v_x_3890_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3944_ = v_x_3890_;
v_isShared_3945_ = v_isSharedCheck_3960_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_vs_3942_);
lean_inc(v_ks_3941_);
lean_dec(v_x_3890_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3960_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_ks_3941_);
lean_ctor_set(v_reuseFailAlloc_3959_, 1, v_vs_3942_);
v___x_3947_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
lean_object* v_newNode_3948_; size_t v___x_3949_; uint8_t v___x_3950_; 
v_newNode_3948_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v___x_3947_, v_x_3893_, v_x_3894_);
v___x_3949_ = ((size_t)7ULL);
v___x_3950_ = lean_usize_dec_le(v___x_3949_, v_x_3892_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3951_; lean_object* v___x_3952_; uint8_t v___x_3953_; 
v___x_3951_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3948_);
v___x_3952_ = lean_unsigned_to_nat(4u);
v___x_3953_ = lean_nat_dec_lt(v___x_3951_, v___x_3952_);
lean_dec(v___x_3951_);
if (v___x_3953_ == 0)
{
lean_object* v_ks_3954_; lean_object* v_vs_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v_ks_3954_ = lean_ctor_get(v_newNode_3948_, 0);
lean_inc_ref(v_ks_3954_);
v_vs_3955_ = lean_ctor_get(v_newNode_3948_, 1);
lean_inc_ref(v_vs_3955_);
lean_dec_ref(v_newNode_3948_);
v___x_3956_ = lean_unsigned_to_nat(0u);
v___x_3957_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0);
v___x_3958_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_x_3892_, v_ks_3954_, v_vs_3955_, v___x_3956_, v___x_3957_);
lean_dec_ref(v_vs_3955_);
lean_dec_ref(v_ks_3954_);
return v___x_3958_;
}
else
{
return v_newNode_3948_;
}
}
else
{
return v_newNode_3948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(size_t v_depth_3961_, lean_object* v_keys_3962_, lean_object* v_vals_3963_, lean_object* v_i_3964_, lean_object* v_entries_3965_){
_start:
{
lean_object* v___x_3966_; uint8_t v___x_3967_; 
v___x_3966_ = lean_array_get_size(v_keys_3962_);
v___x_3967_ = lean_nat_dec_lt(v_i_3964_, v___x_3966_);
if (v___x_3967_ == 0)
{
lean_dec(v_i_3964_);
return v_entries_3965_;
}
else
{
lean_object* v_k_3968_; lean_object* v_v_3969_; uint64_t v___x_3970_; size_t v_h_3971_; size_t v___x_3972_; lean_object* v___x_3973_; size_t v___x_3974_; size_t v___x_3975_; size_t v___x_3976_; size_t v_h_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v_k_3968_ = lean_array_fget_borrowed(v_keys_3962_, v_i_3964_);
v_v_3969_ = lean_array_fget_borrowed(v_vals_3963_, v_i_3964_);
v___x_3970_ = l_Lean_instHashableMVarId_hash(v_k_3968_);
v_h_3971_ = lean_uint64_to_usize(v___x_3970_);
v___x_3972_ = ((size_t)5ULL);
v___x_3973_ = lean_unsigned_to_nat(1u);
v___x_3974_ = ((size_t)1ULL);
v___x_3975_ = lean_usize_sub(v_depth_3961_, v___x_3974_);
v___x_3976_ = lean_usize_mul(v___x_3972_, v___x_3975_);
v_h_3977_ = lean_usize_shift_right(v_h_3971_, v___x_3976_);
v___x_3978_ = lean_nat_add(v_i_3964_, v___x_3973_);
lean_dec(v_i_3964_);
lean_inc(v_v_3969_);
lean_inc(v_k_3968_);
v___x_3979_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_entries_3965_, v_h_3977_, v_depth_3961_, v_k_3968_, v_v_3969_);
v_i_3964_ = v___x_3978_;
v_entries_3965_ = v___x_3979_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_depth_3981_, lean_object* v_keys_3982_, lean_object* v_vals_3983_, lean_object* v_i_3984_, lean_object* v_entries_3985_){
_start:
{
size_t v_depth_boxed_3986_; lean_object* v_res_3987_; 
v_depth_boxed_3986_ = lean_unbox_usize(v_depth_3981_);
lean_dec(v_depth_3981_);
v_res_3987_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_boxed_3986_, v_keys_3982_, v_vals_3983_, v_i_3984_, v_entries_3985_);
lean_dec_ref(v_vals_3983_);
lean_dec_ref(v_keys_3982_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_x_3988_, lean_object* v_x_3989_, lean_object* v_x_3990_, lean_object* v_x_3991_, lean_object* v_x_3992_){
_start:
{
size_t v_x_7806__boxed_3993_; size_t v_x_7807__boxed_3994_; lean_object* v_res_3995_; 
v_x_7806__boxed_3993_ = lean_unbox_usize(v_x_3989_);
lean_dec(v_x_3989_);
v_x_7807__boxed_3994_ = lean_unbox_usize(v_x_3990_);
lean_dec(v_x_3990_);
v_res_3995_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_3988_, v_x_7806__boxed_3993_, v_x_7807__boxed_3994_, v_x_3991_, v_x_3992_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(lean_object* v_x_3996_, lean_object* v_x_3997_, lean_object* v_x_3998_){
_start:
{
uint64_t v___x_3999_; size_t v___x_4000_; size_t v___x_4001_; lean_object* v___x_4002_; 
v___x_3999_ = l_Lean_instHashableMVarId_hash(v_x_3997_);
v___x_4000_ = lean_uint64_to_usize(v___x_3999_);
v___x_4001_ = ((size_t)1ULL);
v___x_4002_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_3996_, v___x_4000_, v___x_4001_, v_x_3997_, v_x_3998_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(lean_object* v_mvarId_4003_, lean_object* v_val_4004_, lean_object* v___y_4005_){
_start:
{
lean_object* v___x_4007_; lean_object* v_mctx_4008_; lean_object* v_cache_4009_; lean_object* v_zetaDeltaFVarIds_4010_; lean_object* v_postponed_4011_; lean_object* v_diag_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4041_; 
v___x_4007_ = lean_st_ref_take(v___y_4005_);
v_mctx_4008_ = lean_ctor_get(v___x_4007_, 0);
v_cache_4009_ = lean_ctor_get(v___x_4007_, 1);
v_zetaDeltaFVarIds_4010_ = lean_ctor_get(v___x_4007_, 2);
v_postponed_4011_ = lean_ctor_get(v___x_4007_, 3);
v_diag_4012_ = lean_ctor_get(v___x_4007_, 4);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4014_ = v___x_4007_;
v_isShared_4015_ = v_isSharedCheck_4041_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_diag_4012_);
lean_inc(v_postponed_4011_);
lean_inc(v_zetaDeltaFVarIds_4010_);
lean_inc(v_cache_4009_);
lean_inc(v_mctx_4008_);
lean_dec(v___x_4007_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4041_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v_depth_4016_; lean_object* v_levelAssignDepth_4017_; lean_object* v_lmvarCounter_4018_; lean_object* v_mvarCounter_4019_; lean_object* v_lDecls_4020_; lean_object* v_decls_4021_; lean_object* v_userNames_4022_; lean_object* v_lAssignment_4023_; lean_object* v_eAssignment_4024_; lean_object* v_dAssignment_4025_; lean_object* v_instanceTypedMVars_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4040_; 
v_depth_4016_ = lean_ctor_get(v_mctx_4008_, 0);
v_levelAssignDepth_4017_ = lean_ctor_get(v_mctx_4008_, 1);
v_lmvarCounter_4018_ = lean_ctor_get(v_mctx_4008_, 2);
v_mvarCounter_4019_ = lean_ctor_get(v_mctx_4008_, 3);
v_lDecls_4020_ = lean_ctor_get(v_mctx_4008_, 4);
v_decls_4021_ = lean_ctor_get(v_mctx_4008_, 5);
v_userNames_4022_ = lean_ctor_get(v_mctx_4008_, 6);
v_lAssignment_4023_ = lean_ctor_get(v_mctx_4008_, 7);
v_eAssignment_4024_ = lean_ctor_get(v_mctx_4008_, 8);
v_dAssignment_4025_ = lean_ctor_get(v_mctx_4008_, 9);
v_instanceTypedMVars_4026_ = lean_ctor_get(v_mctx_4008_, 10);
v_isSharedCheck_4040_ = !lean_is_exclusive(v_mctx_4008_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4028_ = v_mctx_4008_;
v_isShared_4029_ = v_isSharedCheck_4040_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_instanceTypedMVars_4026_);
lean_inc(v_dAssignment_4025_);
lean_inc(v_eAssignment_4024_);
lean_inc(v_lAssignment_4023_);
lean_inc(v_userNames_4022_);
lean_inc(v_decls_4021_);
lean_inc(v_lDecls_4020_);
lean_inc(v_mvarCounter_4019_);
lean_inc(v_lmvarCounter_4018_);
lean_inc(v_levelAssignDepth_4017_);
lean_inc(v_depth_4016_);
lean_dec(v_mctx_4008_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4040_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4033_; 
v___x_4030_ = lean_box(0);
v___x_4031_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_eAssignment_4024_, v_mvarId_4003_, v_val_4004_);
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 8, v___x_4031_);
v___x_4033_ = v___x_4028_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_depth_4016_);
lean_ctor_set(v_reuseFailAlloc_4039_, 1, v_levelAssignDepth_4017_);
lean_ctor_set(v_reuseFailAlloc_4039_, 2, v_lmvarCounter_4018_);
lean_ctor_set(v_reuseFailAlloc_4039_, 3, v_mvarCounter_4019_);
lean_ctor_set(v_reuseFailAlloc_4039_, 4, v_lDecls_4020_);
lean_ctor_set(v_reuseFailAlloc_4039_, 5, v_decls_4021_);
lean_ctor_set(v_reuseFailAlloc_4039_, 6, v_userNames_4022_);
lean_ctor_set(v_reuseFailAlloc_4039_, 7, v_lAssignment_4023_);
lean_ctor_set(v_reuseFailAlloc_4039_, 8, v___x_4031_);
lean_ctor_set(v_reuseFailAlloc_4039_, 9, v_dAssignment_4025_);
lean_ctor_set(v_reuseFailAlloc_4039_, 10, v_instanceTypedMVars_4026_);
v___x_4033_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
lean_object* v___x_4035_; 
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 0, v___x_4033_);
v___x_4035_ = v___x_4014_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v___x_4033_);
lean_ctor_set(v_reuseFailAlloc_4038_, 1, v_cache_4009_);
lean_ctor_set(v_reuseFailAlloc_4038_, 2, v_zetaDeltaFVarIds_4010_);
lean_ctor_set(v_reuseFailAlloc_4038_, 3, v_postponed_4011_);
lean_ctor_set(v_reuseFailAlloc_4038_, 4, v_diag_4012_);
v___x_4035_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4036_ = lean_st_ref_put(v___y_4005_, v___x_4035_);
v___x_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4030_);
return v___x_4037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(lean_object* v_mvarId_4042_, lean_object* v_val_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4042_, v_val_4043_, v___y_4044_);
lean_dec(v___y_4044_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0(lean_object* v_mvar_4049_, uint8_t v_elimTrivial_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v_lctx_4056_; lean_object* v___x_4057_; 
v_lctx_4056_ = lean_ctor_get(v___y_4051_, 2);
lean_inc(v_mvar_4049_);
v___x_4057_ = l_Lean_MVarId_getType(v_mvar_4049_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_object* v_a_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v_a_4058_ = lean_ctor_get(v___x_4057_, 0);
lean_inc(v_a_4058_);
lean_dec_ref_known(v___x_4057_, 1);
v___x_4059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_4060_ = l_Lean_Elab_Tactic_Do_countUses(v_a_4058_, v___x_4059_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v_fst_4062_; lean_object* v_snd_4063_; lean_object* v___x_4064_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v___x_4060_, 1);
v_fst_4062_ = lean_ctor_get(v_a_4061_, 0);
lean_inc(v_fst_4062_);
v_snd_4063_ = lean_ctor_get(v_a_4061_, 1);
lean_inc(v_snd_4063_);
lean_dec(v_a_4061_);
lean_inc_ref(v_lctx_4056_);
v___x_4064_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_lctx_4056_, v_snd_4063_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
if (lean_obj_tag(v___x_4064_) == 0)
{
lean_object* v_a_4065_; lean_object* v___x_4066_; lean_object* v_decls_4067_; lean_object* v___x_4068_; 
v_a_4065_ = lean_ctor_get(v___x_4064_, 0);
lean_inc(v_a_4065_);
lean_dec_ref_known(v___x_4064_, 1);
v___x_4066_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0));
v_decls_4067_ = lean_ctor_get(v_a_4065_, 1);
lean_inc_ref(v_decls_4067_);
lean_dec(v_a_4065_);
v___x_4068_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_4050_, v_decls_4067_, v___x_4066_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
lean_dec_ref(v_decls_4067_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_object* v_a_4069_; lean_object* v_fst_4070_; lean_object* v_snd_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_a_4069_);
lean_dec_ref_known(v___x_4068_, 1);
v_fst_4070_ = lean_ctor_get(v_a_4069_, 0);
lean_inc(v_fst_4070_);
v_snd_4071_ = lean_ctor_get(v_a_4069_, 1);
lean_inc(v_snd_4071_);
lean_dec(v_a_4069_);
v___x_4072_ = l_Lean_Expr_replaceFVars(v_fst_4062_, v_fst_4070_, v_snd_4071_);
lean_dec(v_snd_4071_);
lean_dec(v_fst_4062_);
v___x_4073_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v___x_4072_, v_elimTrivial_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4075_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___x_4073_, 1);
lean_inc(v_mvar_4049_);
v___x_4075_ = l_Lean_MVarId_getTag(v_mvar_4049_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v___x_4077_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_a_4076_);
lean_dec_ref_known(v___x_4075_, 1);
v___x_4077_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4074_, v_a_4076_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; size_t v_sz_4081_; size_t v___x_4082_; lean_object* v___x_4083_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
lean_inc_n(v_a_4078_, 2);
lean_dec_ref_known(v___x_4077_, 1);
v___x_4079_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvar_4049_, v_a_4078_, v___y_4052_);
lean_dec_ref(v___x_4079_);
v___x_4080_ = l_Lean_Expr_mvarId_x21(v_a_4078_);
lean_dec(v_a_4078_);
v_sz_4081_ = lean_array_size(v_fst_4070_);
v___x_4082_ = ((size_t)0ULL);
v___x_4083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_fst_4070_, v_sz_4081_, v___x_4082_, v___x_4080_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
lean_dec_ref(v___y_4051_);
lean_dec(v_fst_4070_);
return v___x_4083_;
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_dec(v_fst_4070_);
lean_dec_ref(v___y_4051_);
lean_dec(v_mvar_4049_);
v_a_4084_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4077_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4077_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec(v_a_4074_);
lean_dec(v_fst_4070_);
lean_dec_ref(v___y_4051_);
lean_dec(v_mvar_4049_);
v_a_4092_ = lean_ctor_get(v___x_4075_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4075_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4075_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
lean_dec(v_fst_4070_);
lean_dec_ref(v___y_4051_);
lean_dec(v_mvar_4049_);
v_a_4100_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4073_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4073_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
else
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
lean_dec(v_fst_4062_);
lean_dec_ref(v___y_4051_);
lean_dec(v_mvar_4049_);
v_a_4108_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4068_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4068_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
else
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4123_; 
lean_dec(v_fst_4062_);
lean_dec_ref(v___y_4051_);
lean_dec(v_mvar_4049_);
v_a_4116_ = lean_ctor_get(v___x_4064_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4118_ = v___x_4064_;
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4064_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4116_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
lean_dec_ref(v___y_4051_);
lean_dec(v_mvar_4049_);
v_a_4124_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4060_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4060_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
else
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
lean_dec_ref(v___y_4051_);
lean_dec(v_mvar_4049_);
v_a_4132_ = lean_ctor_get(v___x_4057_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4134_ = v___x_4057_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4057_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4132_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(lean_object* v_mvar_4140_, lean_object* v_elimTrivial_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
uint8_t v_elimTrivial_boxed_4147_; lean_object* v_res_4148_; 
v_elimTrivial_boxed_4147_ = lean_unbox(v_elimTrivial_4141_);
v_res_4148_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0(v_mvar_4140_, v_elimTrivial_boxed_4147_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets(lean_object* v_mvar_4149_, uint8_t v_elimTrivial_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_){
_start:
{
lean_object* v___x_4156_; lean_object* v___f_4157_; lean_object* v___x_4158_; 
v___x_4156_ = lean_box(v_elimTrivial_4150_);
lean_inc(v_mvar_4149_);
v___f_4157_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4157_, 0, v_mvar_4149_);
lean_closure_set(v___f_4157_, 1, v___x_4156_);
v___x_4158_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvar_4149_, v___f_4157_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___boxed(lean_object* v_mvar_4159_, lean_object* v_elimTrivial_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_){
_start:
{
uint8_t v_elimTrivial_boxed_4166_; lean_object* v_res_4167_; 
v_elimTrivial_boxed_4166_ = lean_unbox(v_elimTrivial_4160_);
v_res_4167_ = l_Lean_Elab_Tactic_Do_elimLets(v_mvar_4159_, v_elimTrivial_boxed_4166_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_);
lean_dec(v_a_4164_);
lean_dec_ref(v_a_4163_);
lean_dec(v_a_4162_);
lean_dec_ref(v_a_4161_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(lean_object* v_mvarId_4168_, lean_object* v_val_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v___x_4175_; 
v___x_4175_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4168_, v_val_4169_, v___y_4171_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(lean_object* v_mvarId_4176_, lean_object* v_val_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
lean_object* v_res_4183_; 
v_res_4183_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(v_mvarId_4176_, v_val_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(lean_object* v_00_u03b2_4184_, lean_object* v_x_4185_, lean_object* v_x_4186_, lean_object* v_x_4187_){
_start:
{
lean_object* v___x_4188_; 
v___x_4188_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_x_4185_, v_x_4186_, v_x_4187_);
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(uint8_t v_elimTrivial_4189_, lean_object* v_as_4190_, size_t v_sz_4191_, size_t v_i_4192_, lean_object* v_b_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_4189_, v_as_4190_, v_sz_4191_, v_i_4192_, v_b_4193_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(lean_object* v_elimTrivial_4200_, lean_object* v_as_4201_, lean_object* v_sz_4202_, lean_object* v_i_4203_, lean_object* v_b_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
uint8_t v_elimTrivial_boxed_4210_; size_t v_sz_boxed_4211_; size_t v_i_boxed_4212_; lean_object* v_res_4213_; 
v_elimTrivial_boxed_4210_ = lean_unbox(v_elimTrivial_4200_);
v_sz_boxed_4211_ = lean_unbox_usize(v_sz_4202_);
lean_dec(v_sz_4202_);
v_i_boxed_4212_ = lean_unbox_usize(v_i_4203_);
lean_dec(v_i_4203_);
v_res_4213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(v_elimTrivial_boxed_4210_, v_as_4201_, v_sz_boxed_4211_, v_i_boxed_4212_, v_b_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
lean_dec_ref(v_as_4201_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_4214_, lean_object* v_x_4215_, size_t v_x_4216_, size_t v_x_4217_, lean_object* v_x_4218_, lean_object* v_x_4219_){
_start:
{
lean_object* v___x_4220_; 
v___x_4220_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4215_, v_x_4216_, v_x_4217_, v_x_4218_, v_x_4219_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_4221_, lean_object* v_x_4222_, lean_object* v_x_4223_, lean_object* v_x_4224_, lean_object* v_x_4225_, lean_object* v_x_4226_){
_start:
{
size_t v_x_8252__boxed_4227_; size_t v_x_8253__boxed_4228_; lean_object* v_res_4229_; 
v_x_8252__boxed_4227_ = lean_unbox_usize(v_x_4223_);
lean_dec(v_x_4223_);
v_x_8253__boxed_4228_ = lean_unbox_usize(v_x_4224_);
lean_dec(v_x_4224_);
v_res_4229_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(v_00_u03b2_4221_, v_x_4222_, v_x_8252__boxed_4227_, v_x_8253__boxed_4228_, v_x_4225_, v_x_4226_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(uint8_t v_elimTrivial_4230_, lean_object* v_as_4231_, size_t v_sz_4232_, size_t v_i_4233_, lean_object* v_b_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
lean_object* v___x_4240_; 
v___x_4240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_4230_, v_as_4231_, v_sz_4232_, v_i_4233_, v_b_4234_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(lean_object* v_elimTrivial_4241_, lean_object* v_as_4242_, lean_object* v_sz_4243_, lean_object* v_i_4244_, lean_object* v_b_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
uint8_t v_elimTrivial_boxed_4251_; size_t v_sz_boxed_4252_; size_t v_i_boxed_4253_; lean_object* v_res_4254_; 
v_elimTrivial_boxed_4251_ = lean_unbox(v_elimTrivial_4241_);
v_sz_boxed_4252_ = lean_unbox_usize(v_sz_4243_);
lean_dec(v_sz_4243_);
v_i_boxed_4253_ = lean_unbox_usize(v_i_4244_);
lean_dec(v_i_4244_);
v_res_4254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(v_elimTrivial_boxed_4251_, v_as_4242_, v_sz_boxed_4252_, v_i_boxed_4253_, v_b_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec_ref(v_as_4242_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(lean_object* v_00_u03b2_4255_, lean_object* v_n_4256_, lean_object* v_k_4257_, lean_object* v_v_4258_){
_start:
{
lean_object* v___x_4259_; 
v___x_4259_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v_n_4256_, v_k_4257_, v_v_4258_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_4260_, size_t v_depth_4261_, lean_object* v_keys_4262_, lean_object* v_vals_4263_, lean_object* v_heq_4264_, lean_object* v_i_4265_, lean_object* v_entries_4266_){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_4261_, v_keys_4262_, v_vals_4263_, v_i_4265_, v_entries_4266_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_4268_, lean_object* v_depth_4269_, lean_object* v_keys_4270_, lean_object* v_vals_4271_, lean_object* v_heq_4272_, lean_object* v_i_4273_, lean_object* v_entries_4274_){
_start:
{
size_t v_depth_boxed_4275_; lean_object* v_res_4276_; 
v_depth_boxed_4275_ = lean_unbox_usize(v_depth_4269_);
lean_dec(v_depth_4269_);
v_res_4276_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_4268_, v_depth_boxed_4275_, v_keys_4270_, v_vals_4271_, v_heq_4272_, v_i_4273_, v_entries_4274_);
lean_dec_ref(v_vals_4271_);
lean_dec_ref(v_keys_4270_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_4277_, lean_object* v_x_4278_, lean_object* v_x_4279_, lean_object* v_x_4280_, lean_object* v_x_4281_){
_start:
{
lean_object* v___x_4282_; 
v___x_4282_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_x_4278_, v_x_4279_, v_x_4280_, v_x_4281_);
return v___x_4282_;
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
