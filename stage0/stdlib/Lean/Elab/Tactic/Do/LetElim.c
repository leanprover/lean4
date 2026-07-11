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
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toCtorIdx___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "uses"};
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 67, 224, 192, 49, 118, 23, 147)}};
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3;
static const lean_closure_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Elab_Tactic_Do_Uses_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(lean_object* v_zero_28_){
_start:
{
lean_inc(v_zero_28_);
return v_zero_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg___boxed(lean_object* v_zero_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(v_zero_29_);
lean_dec(v_zero_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_zero_34_){
_start:
{
lean_inc(v_zero_34_);
return v_zero_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_zero_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_zero_38_);
lean_dec(v_zero_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(lean_object* v_one_41_){
_start:
{
lean_inc(v_one_41_);
return v_one_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg___boxed(lean_object* v_one_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(v_one_42_);
lean_dec(v_one_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_one_47_){
_start:
{
lean_inc(v_one_47_);
return v_one_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_one_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Elab_Tactic_Do_Uses_one_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_one_51_);
lean_dec(v_one_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(lean_object* v_many_54_){
_start:
{
lean_inc(v_many_54_);
return v_many_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg___boxed(lean_object* v_many_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(v_many_55_);
lean_dec(v_many_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_many_60_){
_start:
{
lean_inc(v_many_60_);
return v_many_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_many_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Elab_Tactic_Do_Uses_many_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_many_64_);
lean_dec(v_many_64_);
return v_res_66_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instBEqUses_beq(uint8_t v_x_67_, uint8_t v_y_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_69_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_67_);
v___x_70_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_y_68_);
v___x_71_ = lean_nat_dec_eq(v___x_69_, v___x_70_);
lean_dec(v___x_70_);
lean_dec(v___x_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed(lean_object* v_x_72_, lean_object* v_y_73_){
_start:
{
uint8_t v_x_17__boxed_74_; uint8_t v_y_18__boxed_75_; uint8_t v_res_76_; lean_object* v_r_77_; 
v_x_17__boxed_74_ = lean_unbox(v_x_72_);
v_y_18__boxed_75_ = lean_unbox(v_y_73_);
v_res_76_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_x_17__boxed_74_, v_y_18__boxed_75_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instOrdUses_ord(uint8_t v_x_80_, uint8_t v_y_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_82_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_80_);
v___x_83_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_y_81_);
v___x_84_ = lean_nat_dec_lt(v___x_82_, v___x_83_);
if (v___x_84_ == 0)
{
uint8_t v___x_85_; 
v___x_85_ = lean_nat_dec_eq(v___x_82_, v___x_83_);
lean_dec(v___x_83_);
lean_dec(v___x_82_);
if (v___x_85_ == 0)
{
uint8_t v___x_86_; 
v___x_86_ = 2;
return v___x_86_;
}
else
{
uint8_t v___x_87_; 
v___x_87_ = 1;
return v___x_87_;
}
}
else
{
uint8_t v___x_88_; 
lean_dec(v___x_83_);
lean_dec(v___x_82_);
v___x_88_ = 0;
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed(lean_object* v_x_89_, lean_object* v_y_90_){
_start:
{
uint8_t v_x_30__boxed_91_; uint8_t v_y_31__boxed_92_; uint8_t v_res_93_; lean_object* v_r_94_; 
v_x_30__boxed_91_ = lean_unbox(v_x_89_);
v_y_31__boxed_92_ = lean_unbox(v_y_90_);
v_res_93_ = l_Lean_Elab_Tactic_Do_instOrdUses_ord(v_x_30__boxed_91_, v_y_31__boxed_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_instInhabitedUses_default(void){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_instInhabitedUses(void){
_start:
{
uint8_t v___x_98_; 
v___x_98_ = 0;
return v___x_98_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_add(uint8_t v_x_99_, uint8_t v_x_100_){
_start:
{
if (v_x_99_ == 0)
{
return v_x_100_;
}
else
{
if (v_x_100_ == 0)
{
return v_x_99_;
}
else
{
uint8_t v___x_101_; 
v___x_101_ = 2;
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_add___boxed(lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
uint8_t v_x_30__boxed_104_; uint8_t v_x_31__boxed_105_; uint8_t v_res_106_; lean_object* v_r_107_; 
v_x_30__boxed_104_ = lean_unbox(v_x_102_);
v_x_31__boxed_105_ = lean_unbox(v_x_103_);
v_res_106_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x_30__boxed_104_, v_x_31__boxed_105_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat(uint8_t v_x_108_){
_start:
{
switch(v_x_108_)
{
case 0:
{
lean_object* v___x_109_; 
v___x_109_ = lean_unsigned_to_nat(0u);
return v___x_109_;
}
case 1:
{
lean_object* v___x_110_; 
v___x_110_ = lean_unsigned_to_nat(1u);
return v___x_110_;
}
default: 
{
lean_object* v___x_111_; 
v___x_111_ = lean_unsigned_to_nat(2u);
return v___x_111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat___boxed(lean_object* v_x_112_){
_start:
{
uint8_t v_x_34__boxed_113_; lean_object* v_res_114_; 
v_x_34__boxed_113_ = lean_unbox(v_x_112_);
v_res_114_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v_x_34__boxed_113_);
return v_res_114_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_fromNat(lean_object* v_x_115_){
_start:
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_nat_dec_eq(v_x_115_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(1u);
v___x_119_ = lean_nat_dec_eq(v_x_115_, v___x_118_);
if (v___x_119_ == 0)
{
uint8_t v___x_120_; 
v___x_120_ = 2;
return v___x_120_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 1;
return v___x_121_;
}
}
else
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_fromNat___boxed(lean_object* v_x_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v_x_123_);
lean_dec(v_x_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_129_) == 0)
{
return v_x_128_;
}
else
{
lean_object* v_key_130_; lean_object* v_value_131_; lean_object* v_tail_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_155_; 
v_key_130_ = lean_ctor_get(v_x_129_, 0);
v_value_131_ = lean_ctor_get(v_x_129_, 1);
v_tail_132_ = lean_ctor_get(v_x_129_, 2);
v_isSharedCheck_155_ = !lean_is_exclusive(v_x_129_);
if (v_isSharedCheck_155_ == 0)
{
v___x_134_ = v_x_129_;
v_isShared_135_ = v_isSharedCheck_155_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_tail_132_);
lean_inc(v_value_131_);
lean_inc(v_key_130_);
lean_dec(v_x_129_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_155_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; uint64_t v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v_fold_140_; uint64_t v___x_141_; uint64_t v___x_142_; uint64_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_136_ = lean_array_get_size(v_x_128_);
v___x_137_ = l_Lean_instHashableFVarId_hash(v_key_130_);
v___x_138_ = 32ULL;
v___x_139_ = lean_uint64_shift_right(v___x_137_, v___x_138_);
v_fold_140_ = lean_uint64_xor(v___x_137_, v___x_139_);
v___x_141_ = 16ULL;
v___x_142_ = lean_uint64_shift_right(v_fold_140_, v___x_141_);
v___x_143_ = lean_uint64_xor(v_fold_140_, v___x_142_);
v___x_144_ = lean_uint64_to_usize(v___x_143_);
v___x_145_ = lean_usize_of_nat(v___x_136_);
v___x_146_ = ((size_t)1ULL);
v___x_147_ = lean_usize_sub(v___x_145_, v___x_146_);
v___x_148_ = lean_usize_land(v___x_144_, v___x_147_);
v___x_149_ = lean_array_uget_borrowed(v_x_128_, v___x_148_);
lean_inc(v___x_149_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 2, v___x_149_);
v___x_151_ = v___x_134_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_key_130_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_value_131_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v___x_149_);
v___x_151_ = v_reuseFailAlloc_154_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; 
v___x_152_ = lean_array_uset(v_x_128_, v___x_148_, v___x_151_);
v_x_128_ = v___x_152_;
v_x_129_ = v_tail_132_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(lean_object* v_i_156_, lean_object* v_source_157_, lean_object* v_target_158_){
_start:
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = lean_array_get_size(v_source_157_);
v___x_160_ = lean_nat_dec_lt(v_i_156_, v___x_159_);
if (v___x_160_ == 0)
{
lean_dec_ref(v_source_157_);
lean_dec(v_i_156_);
return v_target_158_;
}
else
{
lean_object* v_es_161_; lean_object* v___x_162_; lean_object* v_source_163_; lean_object* v_target_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v_es_161_ = lean_array_fget(v_source_157_, v_i_156_);
v___x_162_ = lean_box(0);
v_source_163_ = lean_array_fset(v_source_157_, v_i_156_, v___x_162_);
v_target_164_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_target_158_, v_es_161_);
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_nat_add(v_i_156_, v___x_165_);
lean_dec(v_i_156_);
v_i_156_ = v___x_166_;
v_source_157_ = v_source_163_;
v_target_158_ = v_target_164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(lean_object* v_data_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v_nbuckets_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_169_ = lean_array_get_size(v_data_168_);
v___x_170_ = lean_unsigned_to_nat(2u);
v_nbuckets_171_ = lean_nat_mul(v___x_169_, v___x_170_);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_box(0);
v___x_174_ = lean_mk_array(v_nbuckets_171_, v___x_173_);
v___x_175_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v___x_172_, v_data_168_, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(lean_object* v_a_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
uint8_t v___x_178_; 
v___x_178_ = 0;
return v___x_178_;
}
else
{
lean_object* v_key_179_; lean_object* v_tail_180_; uint8_t v___x_181_; 
v_key_179_ = lean_ctor_get(v_x_177_, 0);
v_tail_180_ = lean_ctor_get(v_x_177_, 2);
v___x_181_ = l_Lean_instBEqFVarId_beq(v_key_179_, v_a_176_);
if (v___x_181_ == 0)
{
v_x_177_ = v_tail_180_;
goto _start;
}
else
{
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg___boxed(lean_object* v_a_183_, lean_object* v_x_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_183_, v_x_184_);
lean_dec(v_x_184_);
lean_dec(v_a_183_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(uint8_t v_x3_187_, lean_object* v_x_188_){
_start:
{
if (lean_obj_tag(v_x_188_) == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = lean_box(v_x3_187_);
v___x_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
else
{
lean_object* v_val_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_201_; 
v_val_191_ = lean_ctor_get(v_x_188_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v_x_188_);
if (v_isSharedCheck_201_ == 0)
{
v___x_193_ = v_x_188_;
v_isShared_194_ = v_isSharedCheck_201_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_val_191_);
lean_dec(v_x_188_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_201_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
uint8_t v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_195_ = lean_unbox(v_val_191_);
lean_dec(v_val_191_);
v___x_196_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x3_187_, v___x_195_);
v___x_197_ = lean_box(v___x_196_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_197_);
v___x_199_ = v___x_193_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0___boxed(lean_object* v_x3_202_, lean_object* v_x_203_){
_start:
{
uint8_t v_x3_854__boxed_204_; lean_object* v_res_205_; 
v_x3_854__boxed_204_ = lean_unbox(v_x3_202_);
v_res_205_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_854__boxed_204_, v_x_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(uint8_t v_x3_206_, lean_object* v_a_207_, lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_208_) == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v_val_211_; lean_object* v___x_212_; 
v___x_209_ = lean_box(0);
v___x_210_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_206_, v___x_209_);
v_val_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_val_211_);
lean_dec(v___x_210_);
v___x_212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_212_, 0, v_a_207_);
lean_ctor_set(v___x_212_, 1, v_val_211_);
lean_ctor_set(v___x_212_, 2, v_x_208_);
return v___x_212_;
}
else
{
lean_object* v_key_213_; lean_object* v_value_214_; lean_object* v_tail_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_230_; 
v_key_213_ = lean_ctor_get(v_x_208_, 0);
v_value_214_ = lean_ctor_get(v_x_208_, 1);
v_tail_215_ = lean_ctor_get(v_x_208_, 2);
v_isSharedCheck_230_ = !lean_is_exclusive(v_x_208_);
if (v_isSharedCheck_230_ == 0)
{
v___x_217_ = v_x_208_;
v_isShared_218_ = v_isSharedCheck_230_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_tail_215_);
lean_inc(v_value_214_);
lean_inc(v_key_213_);
lean_dec(v_x_208_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_230_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
uint8_t v___x_219_; 
v___x_219_ = l_Lean_instBEqFVarId_beq(v_key_213_, v_a_207_);
if (v___x_219_ == 0)
{
lean_object* v_tail_220_; lean_object* v___x_222_; 
v_tail_220_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_206_, v_a_207_, v_tail_215_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 2, v_tail_220_);
v___x_222_ = v___x_217_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_key_213_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_value_214_);
lean_ctor_set(v_reuseFailAlloc_223_, 2, v_tail_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_val_226_; lean_object* v___x_228_; 
lean_dec(v_key_213_);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v_value_214_);
v___x_225_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___lam__0(v_x3_206_, v___x_224_);
v_val_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_val_226_);
lean_dec(v___x_225_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v_val_226_);
lean_ctor_set(v___x_217_, 0, v_a_207_);
v___x_228_ = v___x_217_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_207_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_val_226_);
lean_ctor_set(v_reuseFailAlloc_229_, 2, v_tail_215_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2___boxed(lean_object* v_x3_231_, lean_object* v_a_232_, lean_object* v_x_233_){
_start:
{
uint8_t v_x3_886__boxed_234_; lean_object* v_res_235_; 
v_x3_886__boxed_234_ = lean_unbox(v_x3_231_);
v_res_235_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_886__boxed_234_, v_a_232_, v_x_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(uint8_t v_x3_236_, lean_object* v_m_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_size_239_; lean_object* v_buckets_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_289_; 
v_size_239_ = lean_ctor_get(v_m_237_, 0);
v_buckets_240_ = lean_ctor_get(v_m_237_, 1);
v_isSharedCheck_289_ = !lean_is_exclusive(v_m_237_);
if (v_isSharedCheck_289_ == 0)
{
v___x_242_ = v_m_237_;
v_isShared_243_ = v_isSharedCheck_289_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_buckets_240_);
lean_inc(v_size_239_);
lean_dec(v_m_237_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_289_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v_fold_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; lean_object* v_bkt_257_; uint8_t v___x_258_; 
v___x_244_ = lean_array_get_size(v_buckets_240_);
v___x_245_ = l_Lean_instHashableFVarId_hash(v_a_238_);
v___x_246_ = 32ULL;
v___x_247_ = lean_uint64_shift_right(v___x_245_, v___x_246_);
v_fold_248_ = lean_uint64_xor(v___x_245_, v___x_247_);
v___x_249_ = 16ULL;
v___x_250_ = lean_uint64_shift_right(v_fold_248_, v___x_249_);
v___x_251_ = lean_uint64_xor(v_fold_248_, v___x_250_);
v___x_252_ = lean_uint64_to_usize(v___x_251_);
v___x_253_ = lean_usize_of_nat(v___x_244_);
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_sub(v___x_253_, v___x_254_);
v___x_256_ = lean_usize_land(v___x_252_, v___x_255_);
v_bkt_257_ = lean_array_uget_borrowed(v_buckets_240_, v___x_256_);
v___x_258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_238_, v_bkt_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v_size_x27_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_buckets_x27_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_259_ = lean_unsigned_to_nat(1u);
v_size_x27_260_ = lean_nat_add(v_size_239_, v___x_259_);
lean_dec(v_size_239_);
v___x_261_ = lean_box(v_x3_236_);
lean_inc(v_bkt_257_);
v___x_262_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_262_, 0, v_a_238_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
lean_ctor_set(v___x_262_, 2, v_bkt_257_);
v_buckets_x27_263_ = lean_array_uset(v_buckets_240_, v___x_256_, v___x_262_);
v___x_264_ = lean_unsigned_to_nat(4u);
v___x_265_ = lean_nat_mul(v_size_x27_260_, v___x_264_);
v___x_266_ = lean_unsigned_to_nat(3u);
v___x_267_ = lean_nat_div(v___x_265_, v___x_266_);
lean_dec(v___x_265_);
v___x_268_ = lean_array_get_size(v_buckets_x27_263_);
v___x_269_ = lean_nat_dec_le(v___x_267_, v___x_268_);
lean_dec(v___x_267_);
if (v___x_269_ == 0)
{
lean_object* v_val_270_; lean_object* v___x_272_; 
v_val_270_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_263_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v_val_270_);
lean_ctor_set(v___x_242_, 0, v_size_x27_260_);
v___x_272_ = v___x_242_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_size_x27_260_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_val_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
else
{
lean_object* v___x_275_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v_buckets_x27_263_);
lean_ctor_set(v___x_242_, 0, v_size_x27_260_);
v___x_275_ = v___x_242_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_size_x27_260_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_buckets_x27_263_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
else
{
lean_object* v___x_277_; lean_object* v_buckets_x27_278_; lean_object* v_bkt_x27_279_; lean_object* v___y_281_; uint8_t v___x_286_; 
lean_inc(v_bkt_257_);
v___x_277_ = lean_box(0);
v_buckets_x27_278_ = lean_array_uset(v_buckets_240_, v___x_256_, v___x_277_);
lean_inc(v_a_238_);
v_bkt_x27_279_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__2(v_x3_236_, v_a_238_, v_bkt_257_);
v___x_286_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_238_, v_bkt_x27_279_);
lean_dec(v_a_238_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_sub(v_size_239_, v___x_287_);
lean_dec(v_size_239_);
v___y_281_ = v___x_288_;
goto v___jp_280_;
}
else
{
v___y_281_ = v_size_239_;
goto v___jp_280_;
}
v___jp_280_:
{
lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_282_ = lean_array_uset(v_buckets_x27_278_, v___x_256_, v_bkt_x27_279_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_282_);
lean_ctor_set(v___x_242_, 0, v___y_281_);
v___x_284_ = v___x_242_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___y_281_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___boxed(lean_object* v_x3_290_, lean_object* v_m_291_, lean_object* v_a_292_){
_start:
{
uint8_t v_x3_934__boxed_293_; lean_object* v_res_294_; 
v_x3_934__boxed_293_ = lean_unbox(v_x3_290_);
v_res_294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v_x3_934__boxed_293_, v_m_291_, v_a_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
if (lean_obj_tag(v_x_296_) == 0)
{
return v_x_295_;
}
else
{
lean_object* v_key_297_; lean_object* v_value_298_; lean_object* v_tail_299_; uint8_t v___x_300_; lean_object* v___x_301_; 
v_key_297_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_key_297_);
v_value_298_ = lean_ctor_get(v_x_296_, 1);
lean_inc(v_value_298_);
v_tail_299_ = lean_ctor_get(v_x_296_, 2);
lean_inc(v_tail_299_);
lean_dec_ref_known(v_x_296_, 3);
v___x_300_ = lean_unbox(v_value_298_);
lean_dec(v_value_298_);
v___x_301_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v___x_300_, v_x_295_, v_key_297_);
v_x_295_ = v___x_301_;
v_x_296_ = v_tail_299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(lean_object* v_as_303_, size_t v_i_304_, size_t v_stop_305_, lean_object* v_b_306_){
_start:
{
uint8_t v___x_307_; 
v___x_307_ = lean_usize_dec_eq(v_i_304_, v_stop_305_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; size_t v___x_310_; size_t v___x_311_; 
v___x_308_ = lean_array_uget_borrowed(v_as_303_, v_i_304_);
lean_inc(v___x_308_);
v___x_309_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(v_b_306_, v___x_308_);
v___x_310_ = ((size_t)1ULL);
v___x_311_ = lean_usize_add(v_i_304_, v___x_310_);
v_i_304_ = v___x_311_;
v_b_306_ = v___x_309_;
goto _start;
}
else
{
return v_b_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2___boxed(lean_object* v_as_313_, lean_object* v_i_314_, lean_object* v_stop_315_, lean_object* v_b_316_){
_start:
{
size_t v_i_boxed_317_; size_t v_stop_boxed_318_; lean_object* v_res_319_; 
v_i_boxed_317_ = lean_unbox_usize(v_i_314_);
lean_dec(v_i_314_);
v_stop_boxed_318_ = lean_unbox_usize(v_stop_315_);
lean_dec(v_stop_315_);
v_res_319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_as_313_, v_i_boxed_317_, v_stop_boxed_318_, v_b_316_);
lean_dec_ref(v_as_313_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add(lean_object* v_a_320_, lean_object* v_b_321_){
_start:
{
lean_object* v_buckets_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_buckets_322_ = lean_ctor_get(v_a_320_, 1);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_array_get_size(v_buckets_322_);
v___x_325_ = lean_nat_dec_lt(v___x_323_, v___x_324_);
if (v___x_325_ == 0)
{
return v_b_321_;
}
else
{
uint8_t v___x_326_; 
v___x_326_ = lean_nat_dec_le(v___x_324_, v___x_324_);
if (v___x_326_ == 0)
{
if (v___x_325_ == 0)
{
return v_b_321_;
}
else
{
size_t v___x_327_; size_t v___x_328_; lean_object* v___x_329_; 
v___x_327_ = ((size_t)0ULL);
v___x_328_ = lean_usize_of_nat(v___x_324_);
v___x_329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_buckets_322_, v___x_327_, v___x_328_, v_b_321_);
return v___x_329_;
}
}
else
{
size_t v___x_330_; size_t v___x_331_; lean_object* v___x_332_; 
v___x_330_ = ((size_t)0ULL);
v___x_331_ = lean_usize_of_nat(v___x_324_);
v___x_332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_buckets_322_, v___x_330_, v___x_331_, v_b_321_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add___boxed(lean_object* v_a_333_, lean_object* v_b_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_a_333_, v_b_334_);
lean_dec_ref(v_a_333_);
return v_res_335_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(lean_object* v_00_u03b2_336_, lean_object* v_a_337_, lean_object* v_x_338_){
_start:
{
uint8_t v___x_339_; 
v___x_339_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_337_, v_x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___boxed(lean_object* v_00_u03b2_340_, lean_object* v_a_341_, lean_object* v_x_342_){
_start:
{
uint8_t v_res_343_; lean_object* v_r_344_; 
v_res_343_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(v_00_u03b2_340_, v_a_341_, v_x_342_);
lean_dec(v_x_342_);
lean_dec(v_a_341_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1(lean_object* v_00_u03b2_345_, lean_object* v_data_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_data_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_348_, lean_object* v_i_349_, lean_object* v_source_350_, lean_object* v_target_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2___redArg(v_i_349_, v_source_350_, v_target_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1_spec__2_spec__5___redArg(v_x_354_, v_x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(lean_object* v_x_359_){
_start:
{
if (lean_obj_tag(v_x_359_) == 0)
{
lean_object* v___x_360_; 
v___x_360_ = lean_unsigned_to_nat(0u);
return v___x_360_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = lean_unsigned_to_nat(1u);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg___boxed(lean_object* v_x_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(v_x_362_);
lean_dec(v_x_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(lean_object* v_n_364_, lean_object* v_x_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(v_x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___boxed(lean_object* v_n_367_, lean_object* v_x_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(v_n_367_, v_x_368_);
lean_dec(v_x_368_);
lean_dec(v_n_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(lean_object* v_t_370_, lean_object* v_k_371_){
_start:
{
if (lean_obj_tag(v_t_370_) == 0)
{
return v_k_371_;
}
else
{
lean_object* v_uses_372_; lean_object* v___x_373_; 
v_uses_372_ = lean_ctor_get(v_t_370_, 0);
lean_inc_ref(v_uses_372_);
lean_dec_ref_known(v_t_370_, 1);
v___x_373_ = lean_apply_1(v_k_371_, v_uses_372_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(lean_object* v_n_374_, lean_object* v_motive_375_, lean_object* v_ctorIdx_376_, lean_object* v_t_377_, lean_object* v_h_378_, lean_object* v_k_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_377_, v_k_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___boxed(lean_object* v_n_381_, lean_object* v_motive_382_, lean_object* v_ctorIdx_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_k_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(v_n_381_, v_motive_382_, v_ctorIdx_383_, v_t_384_, v_h_385_, v_k_386_);
lean_dec(v_ctorIdx_383_);
lean_dec(v_n_381_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___redArg(lean_object* v_t_388_, lean_object* v_none_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_388_, v_none_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim(lean_object* v_n_391_, lean_object* v_motive_392_, lean_object* v_t_393_, lean_object* v_h_394_, lean_object* v_none_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_393_, v_none_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___boxed(lean_object* v_n_397_, lean_object* v_motive_398_, lean_object* v_t_399_, lean_object* v_h_400_, lean_object* v_none_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Elab_Tactic_Do_BVarUses_none_elim(v_n_397_, v_motive_398_, v_t_399_, v_h_400_, v_none_401_);
lean_dec(v_n_397_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___redArg(lean_object* v_t_403_, lean_object* v_some_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_403_, v_some_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim(lean_object* v_n_406_, lean_object* v_motive_407_, lean_object* v_t_408_, lean_object* v_h_409_, lean_object* v_some_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_408_, v_some_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___boxed(lean_object* v_n_412_, lean_object* v_motive_413_, lean_object* v_t_414_, lean_object* v_h_415_, lean_object* v_some_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Elab_Tactic_Do_BVarUses_some_elim(v_n_412_, v_motive_413_, v_t_414_, v_h_415_, v_some_416_);
lean_dec(v_n_412_);
return v_res_417_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12));
v___x_443_ = l_Lean_mkAtom(v___x_442_);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13);
v___x_445_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_446_ = lean_array_push(v___x_445_, v___x_444_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_447_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14);
v___x_448_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11));
v___x_449_ = lean_box(2);
v___x_450_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v___x_448_);
lean_ctor_set(v___x_450_, 2, v___x_447_);
return v___x_450_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15);
v___x_452_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_453_ = lean_array_push(v___x_452_, v___x_451_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16);
v___x_455_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9));
v___x_456_ = lean_box(2);
v___x_457_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_455_);
lean_ctor_set(v___x_457_, 2, v___x_454_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17);
v___x_459_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_460_ = lean_array_push(v___x_459_, v___x_458_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_461_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18);
v___x_462_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7));
v___x_463_ = lean_box(2);
v___x_464_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___x_462_);
lean_ctor_set(v___x_464_, 2, v___x_461_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19);
v___x_466_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_467_ = lean_array_push(v___x_466_, v___x_465_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_468_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20);
v___x_469_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4));
v___x_470_ = lean_box(2);
v___x_471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_469_);
lean_ctor_set(v___x_471_, 2, v___x_468_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1(void){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21);
return v___x_472_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(lean_object* v_numBVars_473_, lean_object* v_n_474_, lean_object* v_i_475_){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_sub(v_numBVars_473_, v___x_476_);
v___x_478_ = lean_nat_sub(v___x_477_, v_n_474_);
lean_dec(v___x_477_);
v___x_479_ = lean_nat_dec_eq(v_i_475_, v___x_478_);
lean_dec(v___x_478_);
if (v___x_479_ == 0)
{
uint8_t v___x_480_; 
v___x_480_ = 0;
return v___x_480_;
}
else
{
uint8_t v___x_481_; 
v___x_481_ = 1;
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed(lean_object* v_numBVars_482_, lean_object* v_n_483_, lean_object* v_i_484_){
_start:
{
uint8_t v_res_485_; lean_object* v_r_486_; 
v_res_485_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(v_numBVars_482_, v_n_483_, v_i_484_);
lean_dec(v_i_484_);
lean_dec(v_n_483_);
lean_dec(v_numBVars_482_);
v_r_486_ = lean_box(v_res_485_);
return v_r_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(lean_object* v_numBVars_487_, lean_object* v_n_488_){
_start:
{
lean_object* v___f_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
lean_inc(v_numBVars_487_);
v___f_489_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_489_, 0, v_numBVars_487_);
lean_closure_set(v___f_489_, 1, v_n_488_);
v___x_490_ = l_Array_ofFn___redArg(v_numBVars_487_, v___f_489_);
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single(lean_object* v_numBVars_492_, lean_object* v_n_493_, lean_object* v_x_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(v_numBVars_492_, v_n_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop(lean_object* v_numBVars_500_, lean_object* v_x_501_){
_start:
{
if (lean_obj_tag(v_x_501_) == 0)
{
lean_object* v___x_502_; 
v___x_502_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0));
return v___x_502_;
}
else
{
lean_object* v_uses_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_516_; 
v_uses_503_ = lean_ctor_get(v_x_501_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_x_501_);
if (v_isSharedCheck_516_ == 0)
{
v___x_505_ = v_x_501_;
v_isShared_506_ = v_isSharedCheck_516_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_uses_503_);
lean_dec(v_x_501_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_516_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_add(v_numBVars_500_, v___x_507_);
v___x_509_ = lean_nat_sub(v___x_508_, v___x_507_);
lean_dec(v___x_508_);
v___x_510_ = lean_array_fget(v_uses_503_, v___x_509_);
lean_dec(v___x_509_);
v___x_511_ = lean_array_pop(v_uses_503_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_511_);
v___x_513_ = v___x_505_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_515_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; 
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_510_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
return v___x_514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop___boxed(lean_object* v_numBVars_517_, lean_object* v_x_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Elab_Tactic_Do_BVarUses_pop(v_numBVars_517_, v_x_518_);
lean_dec(v_numBVars_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(lean_object* v_as_520_, lean_object* v_bs_521_, lean_object* v_i_522_, lean_object* v_cs_523_){
_start:
{
lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_524_ = lean_array_get_size(v_as_520_);
v___x_525_ = lean_nat_dec_lt(v_i_522_, v___x_524_);
if (v___x_525_ == 0)
{
lean_dec(v_i_522_);
return v_cs_523_;
}
else
{
lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_526_ = lean_array_get_size(v_bs_521_);
v___x_527_ = lean_nat_dec_lt(v_i_522_, v___x_526_);
if (v___x_527_ == 0)
{
lean_dec(v_i_522_);
return v_cs_523_;
}
else
{
lean_object* v_a_528_; lean_object* v_b_529_; uint8_t v___x_530_; uint8_t v___x_531_; uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_a_528_ = lean_array_fget_borrowed(v_as_520_, v_i_522_);
v_b_529_ = lean_array_fget_borrowed(v_bs_521_, v_i_522_);
v___x_530_ = lean_unbox(v_a_528_);
v___x_531_ = lean_unbox(v_b_529_);
v___x_532_ = l_Lean_Elab_Tactic_Do_Uses_add(v___x_530_, v___x_531_);
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_add(v_i_522_, v___x_533_);
lean_dec(v_i_522_);
v___x_535_ = lean_box(v___x_532_);
v___x_536_ = lean_array_push(v_cs_523_, v___x_535_);
v_i_522_ = v___x_534_;
v_cs_523_ = v___x_536_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0___boxed(lean_object* v_as_538_, lean_object* v_bs_539_, lean_object* v_i_540_, lean_object* v_cs_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(v_as_538_, v_bs_539_, v_i_540_, v_cs_541_);
lean_dec_ref(v_bs_539_);
lean_dec_ref(v_as_538_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(lean_object* v_a_545_, lean_object* v_b_546_){
_start:
{
if (lean_obj_tag(v_a_545_) == 0)
{
return v_b_546_;
}
else
{
if (lean_obj_tag(v_b_546_) == 0)
{
lean_object* v_uses_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_uses_547_ = lean_ctor_get(v_a_545_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v_a_545_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v_a_545_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_uses_547_);
lean_dec(v_a_545_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_uses_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
lean_object* v_uses_555_; lean_object* v_uses_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_566_; 
v_uses_555_ = lean_ctor_get(v_a_545_, 0);
lean_inc_ref(v_uses_555_);
lean_dec_ref_known(v_a_545_, 1);
v_uses_556_ = lean_ctor_get(v_b_546_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v_b_546_);
if (v_isSharedCheck_566_ == 0)
{
v___x_558_ = v_b_546_;
v_isShared_559_ = v_isSharedCheck_566_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_uses_556_);
lean_dec(v_b_546_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_566_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0));
v___x_562_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(v_uses_555_, v_uses_556_, v___x_560_, v___x_561_);
lean_dec_ref(v_uses_556_);
lean_dec_ref(v_uses_555_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_562_);
v___x_564_ = v___x_558_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add(lean_object* v_numBVars_567_, lean_object* v_a_568_, lean_object* v_b_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(v_a_568_, v_b_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___boxed(lean_object* v_numBVars_571_, lean_object* v_a_572_, lean_object* v_b_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Elab_Tactic_Do_BVarUses_add(v_numBVars_571_, v_a_572_, v_b_573_);
lean_dec(v_numBVars_571_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instAddBVarUses(lean_object* v_numBVars_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_BVarUses_add___boxed), 3, 1);
lean_closure_set(v___x_576_, 0, v_numBVars_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2___redArg(lean_object* v_f_577_, lean_object* v_x_578_){
_start:
{
lean_object* v_fst_579_; lean_object* v_snd_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_588_; 
v_fst_579_ = lean_ctor_get(v_x_578_, 0);
v_snd_580_ = lean_ctor_get(v_x_578_, 1);
v_isSharedCheck_588_ = !lean_is_exclusive(v_x_578_);
if (v_isSharedCheck_588_ == 0)
{
v___x_582_ = v_x_578_;
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_snd_580_);
lean_inc(v_fst_579_);
lean_dec(v_x_578_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_584_ = lean_apply_1(v_f_577_, v_fst_579_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_584_);
v___x_586_ = v___x_582_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_snd_580_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2(lean_object* v_00_u03b1_u2081_589_, lean_object* v_00_u03b1_u2082_590_, lean_object* v_00_u03b2_591_, lean_object* v_f_592_, lean_object* v_x_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v_f_592_, v_x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0(lean_object* v_x_595_, lean_object* v_new_596_, lean_object* v_x_597_){
_start:
{
lean_inc_ref(v_new_596_);
return v_new_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed(lean_object* v_x_598_, lean_object* v_new_599_, lean_object* v_x_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Elab_Tactic_Do_addMData___lam__0(v_x_598_, v_new_599_, v_x_600_);
lean_dec_ref(v_x_600_);
lean_dec_ref(v_new_599_);
lean_dec(v_x_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData(lean_object* v_d_603_, lean_object* v_e_604_){
_start:
{
if (lean_obj_tag(v_e_604_) == 10)
{
lean_object* v_data_605_; lean_object* v_expr_606_; lean_object* v___f_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_data_605_ = lean_ctor_get(v_e_604_, 0);
lean_inc(v_data_605_);
v_expr_606_ = lean_ctor_get(v_e_604_, 1);
lean_inc_ref(v_expr_606_);
lean_dec_ref_known(v_e_604_, 2);
v___f_607_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_addMData___closed__0));
v___x_608_ = l_Lean_KVMap_mergeBy(v___f_607_, v_d_603_, v_data_605_);
lean_dec(v_data_605_);
v___x_609_ = l_Lean_Expr_mdata___override(v___x_608_, v_expr_606_);
return v___x_609_;
}
else
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Expr_mdata___override(v_d_603_, v_e_604_);
return v___x_610_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(lean_object* v_e_611_){
_start:
{
uint8_t v___y_613_; 
switch(lean_obj_tag(v_e_611_))
{
case 1:
{
uint8_t v___x_615_; 
v___x_615_ = 0;
return v___x_615_;
}
case 5:
{
uint8_t v___x_616_; 
v___x_616_ = l_Lean_Meta_Simp_isOfNatNatLit(v_e_611_);
if (v___x_616_ == 0)
{
uint8_t v___x_617_; 
v___x_617_ = l_Lean_Meta_Simp_isOfScientificLit(v_e_611_);
v___y_613_ = v___x_617_;
goto v___jp_612_;
}
else
{
v___y_613_ = v___x_616_;
goto v___jp_612_;
}
}
case 6:
{
uint8_t v___x_618_; 
v___x_618_ = 0;
return v___x_618_;
}
case 7:
{
uint8_t v___x_619_; 
v___x_619_ = 0;
return v___x_619_;
}
case 8:
{
uint8_t v___x_620_; 
v___x_620_ = 0;
return v___x_620_;
}
case 10:
{
lean_object* v_expr_621_; 
v_expr_621_ = lean_ctor_get(v_e_611_, 1);
v_e_611_ = v_expr_621_;
goto _start;
}
case 11:
{
lean_object* v_struct_623_; 
v_struct_623_ = lean_ctor_get(v_e_611_, 2);
v_e_611_ = v_struct_623_;
goto _start;
}
default: 
{
uint8_t v___x_625_; 
v___x_625_ = 1;
return v___x_625_;
}
}
v___jp_612_:
{
if (v___y_613_ == 0)
{
uint8_t v___x_614_; 
v___x_614_ = l_Lean_Meta_Simp_isCharLit(v_e_611_);
return v___x_614_;
}
else
{
return v___y_613_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup___boxed(lean_object* v_e_626_){
_start:
{
uint8_t v_res_627_; lean_object* v_r_628_; 
v_res_627_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_e_626_);
lean_dec_ref(v_e_626_);
v_r_628_ = lean_box(v_res_627_);
return v_r_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0(lean_object* v_val_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v_val_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(lean_object* v_msgData_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_637_; lean_object* v_env_638_; lean_object* v___x_639_; lean_object* v_mctx_640_; lean_object* v_lctx_641_; lean_object* v_options_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_637_ = lean_st_ref_get(v___y_635_);
v_env_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc_ref(v_env_638_);
lean_dec(v___x_637_);
v___x_639_ = lean_st_ref_get(v___y_633_);
v_mctx_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc_ref(v_mctx_640_);
lean_dec(v___x_639_);
v_lctx_641_ = lean_ctor_get(v___y_632_, 2);
v_options_642_ = lean_ctor_get(v___y_634_, 2);
lean_inc_ref(v_options_642_);
lean_inc_ref(v_lctx_641_);
v___x_643_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_643_, 0, v_env_638_);
lean_ctor_set(v___x_643_, 1, v_mctx_640_);
lean_ctor_set(v___x_643_, 2, v_lctx_641_);
lean_ctor_set(v___x_643_, 3, v_options_642_);
v___x_644_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v_msgData_631_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5___boxed(lean_object* v_msgData_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msgData_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(lean_object* v_msg_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_ref_659_; lean_object* v___x_660_; lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_669_; 
v_ref_659_ = lean_ctor_get(v___y_656_, 5);
v___x_660_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msg_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_669_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_669_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_669_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_667_; 
lean_inc(v_ref_659_);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v_ref_659_);
lean_ctor_set(v___x_665_, 1, v_a_661_);
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 1);
lean_ctor_set(v___x_663_, 0, v___x_665_);
v___x_667_ = v___x_663_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg___boxed(lean_object* v_msg_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__0(lean_object* v_data_677_, lean_object* v_expr_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Expr_mdata___override(v_data_677_, v_expr_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__1(lean_object* v_typeName_680_, lean_object* v_idx_681_, lean_object* v_struct_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Expr_proj___override(v_typeName_680_, v_idx_681_, v_struct_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(lean_object* v_a_684_, lean_object* v_b_685_, lean_object* v_x_686_){
_start:
{
if (lean_obj_tag(v_x_686_) == 0)
{
lean_dec(v_b_685_);
lean_dec(v_a_684_);
return v_x_686_;
}
else
{
lean_object* v_key_687_; lean_object* v_value_688_; lean_object* v_tail_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_701_; 
v_key_687_ = lean_ctor_get(v_x_686_, 0);
v_value_688_ = lean_ctor_get(v_x_686_, 1);
v_tail_689_ = lean_ctor_get(v_x_686_, 2);
v_isSharedCheck_701_ = !lean_is_exclusive(v_x_686_);
if (v_isSharedCheck_701_ == 0)
{
v___x_691_ = v_x_686_;
v_isShared_692_ = v_isSharedCheck_701_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_tail_689_);
lean_inc(v_value_688_);
lean_inc(v_key_687_);
lean_dec(v_x_686_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_701_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
uint8_t v___x_693_; 
v___x_693_ = l_Lean_instBEqFVarId_beq(v_key_687_, v_a_684_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_684_, v_b_685_, v_tail_689_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 2, v___x_694_);
v___x_696_ = v___x_691_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_key_687_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_value_688_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
else
{
lean_object* v___x_699_; 
lean_dec(v_value_688_);
lean_dec(v_key_687_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v_b_685_);
lean_ctor_set(v___x_691_, 0, v_a_684_);
v___x_699_ = v___x_691_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_684_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_b_685_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_tail_689_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(lean_object* v_m_702_, lean_object* v_a_703_, lean_object* v_b_704_){
_start:
{
lean_object* v_size_705_; lean_object* v_buckets_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_749_; 
v_size_705_ = lean_ctor_get(v_m_702_, 0);
v_buckets_706_ = lean_ctor_get(v_m_702_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v_m_702_);
if (v_isSharedCheck_749_ == 0)
{
v___x_708_ = v_m_702_;
v_isShared_709_ = v_isSharedCheck_749_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_buckets_706_);
lean_inc(v_size_705_);
lean_dec(v_m_702_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_749_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; uint64_t v___x_711_; uint64_t v___x_712_; uint64_t v___x_713_; uint64_t v_fold_714_; uint64_t v___x_715_; uint64_t v___x_716_; uint64_t v___x_717_; size_t v___x_718_; size_t v___x_719_; size_t v___x_720_; size_t v___x_721_; size_t v___x_722_; lean_object* v_bkt_723_; uint8_t v___x_724_; 
v___x_710_ = lean_array_get_size(v_buckets_706_);
v___x_711_ = l_Lean_instHashableFVarId_hash(v_a_703_);
v___x_712_ = 32ULL;
v___x_713_ = lean_uint64_shift_right(v___x_711_, v___x_712_);
v_fold_714_ = lean_uint64_xor(v___x_711_, v___x_713_);
v___x_715_ = 16ULL;
v___x_716_ = lean_uint64_shift_right(v_fold_714_, v___x_715_);
v___x_717_ = lean_uint64_xor(v_fold_714_, v___x_716_);
v___x_718_ = lean_uint64_to_usize(v___x_717_);
v___x_719_ = lean_usize_of_nat(v___x_710_);
v___x_720_ = ((size_t)1ULL);
v___x_721_ = lean_usize_sub(v___x_719_, v___x_720_);
v___x_722_ = lean_usize_land(v___x_718_, v___x_721_);
v_bkt_723_ = lean_array_uget_borrowed(v_buckets_706_, v___x_722_);
v___x_724_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_703_, v_bkt_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v_size_x27_726_; lean_object* v___x_727_; lean_object* v_buckets_x27_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_725_ = lean_unsigned_to_nat(1u);
v_size_x27_726_ = lean_nat_add(v_size_705_, v___x_725_);
lean_dec(v_size_705_);
lean_inc(v_bkt_723_);
v___x_727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_727_, 0, v_a_703_);
lean_ctor_set(v___x_727_, 1, v_b_704_);
lean_ctor_set(v___x_727_, 2, v_bkt_723_);
v_buckets_x27_728_ = lean_array_uset(v_buckets_706_, v___x_722_, v___x_727_);
v___x_729_ = lean_unsigned_to_nat(4u);
v___x_730_ = lean_nat_mul(v_size_x27_726_, v___x_729_);
v___x_731_ = lean_unsigned_to_nat(3u);
v___x_732_ = lean_nat_div(v___x_730_, v___x_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_array_get_size(v_buckets_x27_728_);
v___x_734_ = lean_nat_dec_le(v___x_732_, v___x_733_);
lean_dec(v___x_732_);
if (v___x_734_ == 0)
{
lean_object* v_val_735_; lean_object* v___x_737_; 
v_val_735_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__1___redArg(v_buckets_x27_728_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v_val_735_);
lean_ctor_set(v___x_708_, 0, v_size_x27_726_);
v___x_737_ = v___x_708_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_size_x27_726_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_val_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
else
{
lean_object* v___x_740_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v_buckets_x27_728_);
lean_ctor_set(v___x_708_, 0, v_size_x27_726_);
v___x_740_ = v___x_708_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_size_x27_726_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_buckets_x27_728_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
else
{
lean_object* v___x_742_; lean_object* v_buckets_x27_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
lean_inc(v_bkt_723_);
v___x_742_ = lean_box(0);
v_buckets_x27_743_ = lean_array_uset(v_buckets_706_, v___x_722_, v___x_742_);
v___x_744_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_703_, v_b_704_, v_bkt_723_);
v___x_745_ = lean_array_uset(v_buckets_x27_743_, v___x_722_, v___x_744_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v___x_745_);
v___x_747_ = v___x_708_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_size_705_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(lean_object* v___y_750_){
_start:
{
lean_object* v___x_752_; lean_object* v_ngen_753_; lean_object* v_namePrefix_754_; lean_object* v_idx_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_784_; 
v___x_752_ = lean_st_ref_get(v___y_750_);
v_ngen_753_ = lean_ctor_get(v___x_752_, 2);
lean_inc_ref(v_ngen_753_);
lean_dec(v___x_752_);
v_namePrefix_754_ = lean_ctor_get(v_ngen_753_, 0);
v_idx_755_ = lean_ctor_get(v_ngen_753_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v_ngen_753_);
if (v_isSharedCheck_784_ == 0)
{
v___x_757_ = v_ngen_753_;
v_isShared_758_ = v_isSharedCheck_784_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_idx_755_);
lean_inc(v_namePrefix_754_);
lean_dec(v_ngen_753_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_784_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v_env_760_; lean_object* v_nextMacroScope_761_; lean_object* v_auxDeclNGen_762_; lean_object* v_traceState_763_; lean_object* v_cache_764_; lean_object* v_messages_765_; lean_object* v_infoState_766_; lean_object* v_snapshotTasks_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_782_; 
v___x_759_ = lean_st_ref_take(v___y_750_);
v_env_760_ = lean_ctor_get(v___x_759_, 0);
v_nextMacroScope_761_ = lean_ctor_get(v___x_759_, 1);
v_auxDeclNGen_762_ = lean_ctor_get(v___x_759_, 3);
v_traceState_763_ = lean_ctor_get(v___x_759_, 4);
v_cache_764_ = lean_ctor_get(v___x_759_, 5);
v_messages_765_ = lean_ctor_get(v___x_759_, 6);
v_infoState_766_ = lean_ctor_get(v___x_759_, 7);
v_snapshotTasks_767_ = lean_ctor_get(v___x_759_, 8);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v___x_759_, 2);
lean_dec(v_unused_783_);
v___x_769_ = v___x_759_;
v_isShared_770_ = v_isSharedCheck_782_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_snapshotTasks_767_);
lean_inc(v_infoState_766_);
lean_inc(v_messages_765_);
lean_inc(v_cache_764_);
lean_inc(v_traceState_763_);
lean_inc(v_auxDeclNGen_762_);
lean_inc(v_nextMacroScope_761_);
lean_inc(v_env_760_);
lean_dec(v___x_759_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_782_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_r_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
lean_inc(v_idx_755_);
lean_inc(v_namePrefix_754_);
v_r_771_ = l_Lean_Name_num___override(v_namePrefix_754_, v_idx_755_);
v___x_772_ = lean_unsigned_to_nat(1u);
v___x_773_ = lean_nat_add(v_idx_755_, v___x_772_);
lean_dec(v_idx_755_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v___x_773_);
v___x_775_ = v___x_757_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_namePrefix_754_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_781_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_777_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 2, v___x_775_);
v___x_777_ = v___x_769_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_env_760_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_nextMacroScope_761_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_780_, 3, v_auxDeclNGen_762_);
lean_ctor_set(v_reuseFailAlloc_780_, 4, v_traceState_763_);
lean_ctor_set(v_reuseFailAlloc_780_, 5, v_cache_764_);
lean_ctor_set(v_reuseFailAlloc_780_, 6, v_messages_765_);
lean_ctor_set(v_reuseFailAlloc_780_, 7, v_infoState_766_);
lean_ctor_set(v_reuseFailAlloc_780_, 8, v_snapshotTasks_767_);
v___x_777_ = v_reuseFailAlloc_780_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_st_ref_set(v___y_750_, v___x_777_);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v_r_771_);
return v___x_779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg___boxed(lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_785_);
lean_dec(v___y_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
v___x_793_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_791_);
v_a_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5___boxed(lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(lean_object* v_a_808_, lean_object* v_x_809_){
_start:
{
if (lean_obj_tag(v_x_809_) == 0)
{
return v_x_809_;
}
else
{
lean_object* v_key_810_; lean_object* v_value_811_; lean_object* v_tail_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_821_; 
v_key_810_ = lean_ctor_get(v_x_809_, 0);
v_value_811_ = lean_ctor_get(v_x_809_, 1);
v_tail_812_ = lean_ctor_get(v_x_809_, 2);
v_isSharedCheck_821_ = !lean_is_exclusive(v_x_809_);
if (v_isSharedCheck_821_ == 0)
{
v___x_814_ = v_x_809_;
v_isShared_815_ = v_isSharedCheck_821_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_tail_812_);
lean_inc(v_value_811_);
lean_inc(v_key_810_);
lean_dec(v_x_809_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_821_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
uint8_t v___x_816_; 
v___x_816_ = l_Lean_instBEqFVarId_beq(v_key_810_, v_a_808_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_808_, v_tail_812_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 2, v___x_817_);
v___x_819_ = v___x_814_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_key_810_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_value_811_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
else
{
lean_del_object(v___x_814_);
lean_dec(v_value_811_);
lean_dec(v_key_810_);
return v_tail_812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(lean_object* v_a_822_, lean_object* v_x_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_822_, v_x_823_);
lean_dec(v_a_822_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(lean_object* v_m_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_size_827_; lean_object* v_buckets_828_; lean_object* v___x_829_; uint64_t v___x_830_; uint64_t v___x_831_; uint64_t v___x_832_; uint64_t v_fold_833_; uint64_t v___x_834_; uint64_t v___x_835_; uint64_t v___x_836_; size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; size_t v___x_840_; size_t v___x_841_; lean_object* v_bkt_842_; uint8_t v___x_843_; 
v_size_827_ = lean_ctor_get(v_m_825_, 0);
v_buckets_828_ = lean_ctor_get(v_m_825_, 1);
v___x_829_ = lean_array_get_size(v_buckets_828_);
v___x_830_ = l_Lean_instHashableFVarId_hash(v_a_826_);
v___x_831_ = 32ULL;
v___x_832_ = lean_uint64_shift_right(v___x_830_, v___x_831_);
v_fold_833_ = lean_uint64_xor(v___x_830_, v___x_832_);
v___x_834_ = 16ULL;
v___x_835_ = lean_uint64_shift_right(v_fold_833_, v___x_834_);
v___x_836_ = lean_uint64_xor(v_fold_833_, v___x_835_);
v___x_837_ = lean_uint64_to_usize(v___x_836_);
v___x_838_ = lean_usize_of_nat(v___x_829_);
v___x_839_ = ((size_t)1ULL);
v___x_840_ = lean_usize_sub(v___x_838_, v___x_839_);
v___x_841_ = lean_usize_land(v___x_837_, v___x_840_);
v_bkt_842_ = lean_array_uget_borrowed(v_buckets_828_, v___x_841_);
v___x_843_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_a_826_, v_bkt_842_);
if (v___x_843_ == 0)
{
return v_m_825_;
}
else
{
lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_856_; 
lean_inc(v_bkt_842_);
lean_inc_ref(v_buckets_828_);
lean_inc(v_size_827_);
v_isSharedCheck_856_ = !lean_is_exclusive(v_m_825_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; lean_object* v_unused_858_; 
v_unused_857_ = lean_ctor_get(v_m_825_, 1);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v_m_825_, 0);
lean_dec(v_unused_858_);
v___x_845_ = v_m_825_;
v_isShared_846_ = v_isSharedCheck_856_;
goto v_resetjp_844_;
}
else
{
lean_dec(v_m_825_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_856_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v_buckets_x27_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_847_ = lean_box(0);
v_buckets_x27_848_ = lean_array_uset(v_buckets_828_, v___x_841_, v___x_847_);
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = lean_nat_sub(v_size_827_, v___x_849_);
lean_dec(v_size_827_);
v___x_851_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_826_, v_bkt_842_);
v___x_852_ = lean_array_uset(v_buckets_x27_848_, v___x_841_, v___x_851_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v___x_852_);
lean_ctor_set(v___x_845_, 0, v___x_850_);
v___x_854_ = v___x_845_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(lean_object* v_m_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_859_, v_a_860_);
lean_dec(v_a_860_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(lean_object* v_a_862_, lean_object* v_fallback_863_, lean_object* v_x_864_){
_start:
{
if (lean_obj_tag(v_x_864_) == 0)
{
lean_inc(v_fallback_863_);
return v_fallback_863_;
}
else
{
lean_object* v_key_865_; lean_object* v_value_866_; lean_object* v_tail_867_; uint8_t v___x_868_; 
v_key_865_ = lean_ctor_get(v_x_864_, 0);
v_value_866_ = lean_ctor_get(v_x_864_, 1);
v_tail_867_ = lean_ctor_get(v_x_864_, 2);
v___x_868_ = l_Lean_instBEqFVarId_beq(v_key_865_, v_a_862_);
if (v___x_868_ == 0)
{
v_x_864_ = v_tail_867_;
goto _start;
}
else
{
lean_inc(v_value_866_);
return v_value_866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(lean_object* v_a_870_, lean_object* v_fallback_871_, lean_object* v_x_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_870_, v_fallback_871_, v_x_872_);
lean_dec(v_x_872_);
lean_dec(v_fallback_871_);
lean_dec(v_a_870_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(lean_object* v_m_874_, lean_object* v_a_875_, lean_object* v_fallback_876_){
_start:
{
lean_object* v_buckets_877_; lean_object* v___x_878_; uint64_t v___x_879_; uint64_t v___x_880_; uint64_t v___x_881_; uint64_t v_fold_882_; uint64_t v___x_883_; uint64_t v___x_884_; uint64_t v___x_885_; size_t v___x_886_; size_t v___x_887_; size_t v___x_888_; size_t v___x_889_; size_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_buckets_877_ = lean_ctor_get(v_m_874_, 1);
v___x_878_ = lean_array_get_size(v_buckets_877_);
v___x_879_ = l_Lean_instHashableFVarId_hash(v_a_875_);
v___x_880_ = 32ULL;
v___x_881_ = lean_uint64_shift_right(v___x_879_, v___x_880_);
v_fold_882_ = lean_uint64_xor(v___x_879_, v___x_881_);
v___x_883_ = 16ULL;
v___x_884_ = lean_uint64_shift_right(v_fold_882_, v___x_883_);
v___x_885_ = lean_uint64_xor(v_fold_882_, v___x_884_);
v___x_886_ = lean_uint64_to_usize(v___x_885_);
v___x_887_ = lean_usize_of_nat(v___x_878_);
v___x_888_ = ((size_t)1ULL);
v___x_889_ = lean_usize_sub(v___x_887_, v___x_888_);
v___x_890_ = lean_usize_land(v___x_886_, v___x_889_);
v___x_891_ = lean_array_uget_borrowed(v_buckets_877_, v___x_890_);
v___x_892_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_875_, v_fallback_876_, v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(lean_object* v_m_893_, lean_object* v_a_894_, lean_object* v_fallback_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_893_, v_a_894_, v_fallback_895_);
lean_dec(v_fallback_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_m_893_);
return v_res_896_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_900_ = lean_box(0);
v___x_901_ = lean_unsigned_to_nat(16u);
v___x_902_ = lean_mk_array(v___x_901_, v___x_900_);
return v___x_902_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2);
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___x_903_);
return v___x_905_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__1(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__0));
v___x_909_ = l_Lean_stringToMessageData(v___x_908_);
return v___x_909_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__3(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__2));
v___x_912_ = l_Lean_stringToMessageData(v___x_911_);
return v___x_912_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__5(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__4));
v___x_915_ = l_Lean_stringToMessageData(v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses(lean_object* v_e_916_, lean_object* v_subst_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
switch(lean_obj_tag(v_e_916_))
{
case 0:
{
lean_object* v_deBruijnIndex_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_deBruijnIndex_923_ = lean_ctor_get(v_e_916_, 0);
v___x_924_ = lean_array_get_size(v_subst_917_);
v___x_925_ = lean_nat_dec_lt(v_deBruijnIndex_923_, v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_inc(v_deBruijnIndex_923_);
lean_dec_ref_known(v_e_916_, 1);
lean_dec_ref(v_subst_917_);
v___x_926_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__1, &l_Lean_Elab_Tactic_Do_countUses___closed__1_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__1);
v___x_927_ = l_Nat_reprFast(v_deBruijnIndex_923_);
v___x_928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
v___x_929_ = l_Lean_MessageData_ofFormat(v___x_928_);
v___x_930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_926_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__3, &l_Lean_Elab_Tactic_Do_countUses___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__3);
v___x_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Nat_reprFast(v___x_924_);
v___x_934_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
v___x_935_ = l_Lean_MessageData_ofFormat(v___x_934_);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_932_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_936_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
return v___x_937_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_938_ = lean_unsigned_to_nat(1u);
v___x_939_ = lean_nat_sub(v___x_924_, v___x_938_);
v___x_940_ = lean_nat_sub(v___x_939_, v_deBruijnIndex_923_);
lean_dec(v___x_939_);
v___x_941_ = lean_array_fget(v_subst_917_, v___x_940_);
lean_dec(v___x_940_);
lean_dec_ref(v_subst_917_);
v___x_942_ = 1;
v___x_943_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_944_ = lean_box(v___x_942_);
v___x_945_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_943_, v___x_941_, v___x_944_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v_e_916_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
return v___x_947_;
}
}
case 1:
{
lean_object* v_fvarId_948_; uint8_t v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
lean_dec_ref(v_subst_917_);
v_fvarId_948_ = lean_ctor_get(v_e_916_, 0);
v___x_949_ = 1;
v___x_950_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_951_ = lean_box(v___x_949_);
lean_inc(v_fvarId_948_);
v___x_952_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v___x_950_, v_fvarId_948_, v___x_951_);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v_e_916_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
case 5:
{
lean_object* v_fn_955_; lean_object* v_arg_956_; lean_object* v___x_957_; 
v_fn_955_ = lean_ctor_get(v_e_916_, 0);
lean_inc_ref(v_fn_955_);
v_arg_956_ = lean_ctor_get(v_e_916_, 1);
lean_inc_ref(v_arg_956_);
lean_dec_ref_known(v_e_916_, 2);
lean_inc_ref(v_subst_917_);
v___x_957_ = l_Lean_Elab_Tactic_Do_countUses(v_fn_955_, v_subst_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v_fst_959_; lean_object* v_snd_960_; lean_object* v___x_961_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
v_fst_959_ = lean_ctor_get(v_a_958_, 0);
lean_inc(v_fst_959_);
v_snd_960_ = lean_ctor_get(v_a_958_, 1);
lean_inc(v_snd_960_);
lean_dec(v_a_958_);
v___x_961_ = l_Lean_Elab_Tactic_Do_countUses(v_arg_956_, v_subst_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_980_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_980_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_980_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_980_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v_fst_966_; lean_object* v_snd_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_979_; 
v_fst_966_ = lean_ctor_get(v_a_962_, 0);
v_snd_967_ = lean_ctor_get(v_a_962_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v_a_962_);
if (v_isSharedCheck_979_ == 0)
{
v___x_969_ = v_a_962_;
v_isShared_970_ = v_isSharedCheck_979_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_snd_967_);
lean_inc(v_fst_966_);
lean_dec(v_a_962_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_979_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_971_ = l_Lean_Expr_app___override(v_fst_959_, v_fst_966_);
v___x_972_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_960_, v_snd_967_);
lean_dec(v_snd_960_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v___x_972_);
lean_ctor_set(v___x_969_, 0, v___x_971_);
v___x_974_ = v___x_969_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v___x_972_);
v___x_974_ = v_reuseFailAlloc_978_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_976_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_974_);
v___x_976_ = v___x_964_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
else
{
lean_dec(v_snd_960_);
lean_dec(v_fst_959_);
return v___x_961_;
}
}
else
{
lean_dec_ref(v_arg_956_);
lean_dec_ref(v_subst_917_);
return v___x_957_;
}
}
case 6:
{
lean_object* v_binderName_981_; lean_object* v_binderType_982_; lean_object* v_body_983_; uint8_t v_binderInfo_984_; lean_object* v___x_985_; 
v_binderName_981_ = lean_ctor_get(v_e_916_, 0);
lean_inc(v_binderName_981_);
v_binderType_982_ = lean_ctor_get(v_e_916_, 1);
lean_inc_ref(v_binderType_982_);
v_body_983_ = lean_ctor_get(v_e_916_, 2);
lean_inc_ref(v_body_983_);
v_binderInfo_984_ = lean_ctor_get_uint8(v_e_916_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_916_, 3);
v___x_985_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_987_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
lean_inc_ref(v_subst_917_);
v___x_987_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_982_, v_subst_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v_fst_989_; lean_object* v_snd_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v_fst_989_ = lean_ctor_get(v_a_988_, 0);
lean_inc(v_fst_989_);
v_snd_990_ = lean_ctor_get(v_a_988_, 1);
lean_inc(v_snd_990_);
lean_dec(v_a_988_);
lean_inc(v_a_986_);
v___x_991_ = lean_array_push(v_subst_917_, v_a_986_);
v___x_992_ = l_Lean_Elab_Tactic_Do_countUses(v_body_983_, v___x_991_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1012_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1012_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1012_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v_fst_997_; lean_object* v_snd_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1011_; 
v_fst_997_ = lean_ctor_get(v_a_993_, 0);
v_snd_998_ = lean_ctor_get(v_a_993_, 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_a_993_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1000_ = v_a_993_;
v_isShared_1001_ = v_isSharedCheck_1011_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_snd_998_);
lean_inc(v_fst_997_);
lean_dec(v_a_993_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1011_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1002_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_990_, v_snd_998_);
lean_dec(v_snd_990_);
v___x_1003_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_1002_, v_a_986_);
lean_dec(v_a_986_);
v___x_1004_ = l_Lean_Expr_lam___override(v_binderName_981_, v_fst_989_, v_fst_997_, v_binderInfo_984_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 1, v___x_1003_);
lean_ctor_set(v___x_1000_, 0, v___x_1004_);
v___x_1006_ = v___x_1000_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v___x_1003_);
v___x_1006_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1008_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1006_);
v___x_1008_ = v___x_995_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
else
{
lean_dec(v_snd_990_);
lean_dec(v_fst_989_);
lean_dec(v_a_986_);
lean_dec(v_binderName_981_);
return v___x_992_;
}
}
else
{
lean_dec(v_a_986_);
lean_dec_ref(v_body_983_);
lean_dec(v_binderName_981_);
lean_dec_ref(v_subst_917_);
return v___x_987_;
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec_ref(v_body_983_);
lean_dec_ref(v_binderType_982_);
lean_dec(v_binderName_981_);
lean_dec_ref(v_subst_917_);
v_a_1013_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_985_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_985_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1021_; lean_object* v_binderType_1022_; lean_object* v_body_1023_; uint8_t v_binderInfo_1024_; lean_object* v___x_1025_; 
v_binderName_1021_ = lean_ctor_get(v_e_916_, 0);
lean_inc(v_binderName_1021_);
v_binderType_1022_ = lean_ctor_get(v_e_916_, 1);
lean_inc_ref(v_binderType_1022_);
v_body_1023_ = lean_ctor_get(v_e_916_, 2);
lean_inc_ref(v_body_1023_);
v_binderInfo_1024_ = lean_ctor_get_uint8(v_e_916_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_916_, 3);
v___x_1025_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
lean_inc_ref(v_subst_917_);
v___x_1027_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_1022_, v_subst_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v_fst_1029_; lean_object* v_snd_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v_fst_1029_ = lean_ctor_get(v_a_1028_, 0);
lean_inc(v_fst_1029_);
v_snd_1030_ = lean_ctor_get(v_a_1028_, 1);
lean_inc(v_snd_1030_);
lean_dec(v_a_1028_);
lean_inc(v_a_1026_);
v___x_1031_ = lean_array_push(v_subst_917_, v_a_1026_);
v___x_1032_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1023_, v___x_1031_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1052_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1052_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1052_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_fst_1037_; lean_object* v_snd_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1051_; 
v_fst_1037_ = lean_ctor_get(v_a_1033_, 0);
v_snd_1038_ = lean_ctor_get(v_a_1033_, 1);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_a_1033_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1040_ = v_a_1033_;
v_isShared_1041_ = v_isSharedCheck_1051_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_snd_1038_);
lean_inc(v_fst_1037_);
lean_dec(v_a_1033_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1051_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1042_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_snd_1030_, v_snd_1038_);
lean_dec(v_snd_1030_);
v___x_1043_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_1042_, v_a_1026_);
lean_dec(v_a_1026_);
v___x_1044_ = l_Lean_Expr_forallE___override(v_binderName_1021_, v_fst_1029_, v_fst_1037_, v_binderInfo_1024_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 1, v___x_1043_);
lean_ctor_set(v___x_1040_, 0, v___x_1044_);
v___x_1046_ = v___x_1040_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_1043_);
v___x_1046_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1048_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1046_);
v___x_1048_ = v___x_1035_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
else
{
lean_dec(v_snd_1030_);
lean_dec(v_fst_1029_);
lean_dec(v_a_1026_);
lean_dec(v_binderName_1021_);
return v___x_1032_;
}
}
else
{
lean_dec(v_a_1026_);
lean_dec_ref(v_body_1023_);
lean_dec(v_binderName_1021_);
lean_dec_ref(v_subst_917_);
return v___x_1027_;
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec_ref(v_body_1023_);
lean_dec_ref(v_binderType_1022_);
lean_dec(v_binderName_1021_);
lean_dec_ref(v_subst_917_);
v_a_1053_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1025_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1025_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
case 8:
{
lean_object* v_declName_1061_; lean_object* v_type_1062_; lean_object* v_value_1063_; lean_object* v_body_1064_; uint8_t v_nondep_1065_; lean_object* v___x_1066_; 
v_declName_1061_ = lean_ctor_get(v_e_916_, 0);
lean_inc(v_declName_1061_);
v_type_1062_ = lean_ctor_get(v_e_916_, 1);
lean_inc_ref(v_type_1062_);
v_value_1063_ = lean_ctor_get(v_e_916_, 2);
lean_inc_ref(v_value_1063_);
v_body_1064_ = lean_ctor_get(v_e_916_, 3);
lean_inc_ref(v_body_1064_);
v_nondep_1065_ = lean_ctor_get_uint8(v_e_916_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_916_, 4);
v___x_1066_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5(v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc_n(v_a_1067_, 2);
lean_dec_ref_known(v___x_1066_, 1);
lean_inc_ref(v_subst_917_);
v___x_1068_ = lean_array_push(v_subst_917_, v_a_1067_);
v___x_1069_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1064_, v___x_1068_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1112_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1112_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1112_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v_fst_1074_; lean_object* v_snd_1075_; lean_object* v___x_1077_; 
v_fst_1074_ = lean_ctor_get(v_a_1070_, 0);
lean_inc(v_fst_1074_);
v_snd_1075_ = lean_ctor_get(v_a_1070_, 1);
lean_inc(v_snd_1075_);
lean_dec(v_a_1070_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set_tag(v___x_1072_, 1);
lean_ctor_set(v___x_1072_, 0, v_value_1063_);
v___x_1077_ = v___x_1072_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_value_1063_);
v___x_1077_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_a_1067_, v_type_1062_, v___x_1077_, v_snd_1075_, v_subst_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
lean_dec(v_a_1067_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1102_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1102_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1102_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v_snd_1083_; lean_object* v_fst_1084_; 
v_snd_1083_ = lean_ctor_get(v_a_1079_, 1);
lean_inc(v_snd_1083_);
v_fst_1084_ = lean_ctor_get(v_snd_1083_, 0);
lean_inc(v_fst_1084_);
if (lean_obj_tag(v_fst_1084_) == 1)
{
lean_object* v_fst_1085_; lean_object* v_snd_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1098_; 
v_fst_1085_ = lean_ctor_get(v_a_1079_, 0);
lean_inc(v_fst_1085_);
lean_dec(v_a_1079_);
v_snd_1086_ = lean_ctor_get(v_snd_1083_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_snd_1083_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; 
v_unused_1099_ = lean_ctor_get(v_snd_1083_, 0);
lean_dec(v_unused_1099_);
v___x_1088_ = v_snd_1083_;
v_isShared_1089_ = v_isSharedCheck_1098_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_snd_1086_);
lean_dec(v_snd_1083_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1098_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_val_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v_val_1090_ = lean_ctor_get(v_fst_1084_, 0);
lean_inc(v_val_1090_);
lean_dec_ref_known(v_fst_1084_, 1);
v___x_1091_ = l_Lean_Expr_letE___override(v_declName_1061_, v_fst_1085_, v_val_1090_, v_fst_1074_, v_nondep_1065_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1091_);
v___x_1093_ = v___x_1088_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_snd_1086_);
v___x_1093_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1095_; 
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1093_);
v___x_1095_ = v___x_1081_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v_fst_1084_);
lean_dec(v_snd_1083_);
lean_del_object(v___x_1081_);
lean_dec(v_a_1079_);
lean_dec(v_fst_1074_);
lean_dec(v_declName_1061_);
v___x_1100_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__5, &l_Lean_Elab_Tactic_Do_countUses___closed__5_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__5);
v___x_1101_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_1100_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
return v___x_1101_;
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v_fst_1074_);
lean_dec(v_declName_1061_);
v_a_1103_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1078_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1078_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1067_);
lean_dec_ref(v_value_1063_);
lean_dec_ref(v_type_1062_);
lean_dec(v_declName_1061_);
lean_dec_ref(v_subst_917_);
return v___x_1069_;
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec_ref(v_body_1064_);
lean_dec_ref(v_value_1063_);
lean_dec_ref(v_type_1062_);
lean_dec(v_declName_1061_);
lean_dec_ref(v_subst_917_);
v_a_1113_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1066_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1066_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
case 10:
{
lean_object* v_data_1121_; lean_object* v_expr_1122_; lean_object* v___x_1123_; 
v_data_1121_ = lean_ctor_get(v_e_916_, 0);
lean_inc(v_data_1121_);
v_expr_1122_ = lean_ctor_get(v_e_916_, 1);
lean_inc_ref(v_expr_1122_);
lean_dec_ref_known(v_e_916_, 2);
v___x_1123_ = l_Lean_Elab_Tactic_Do_countUses(v_expr_1122_, v_subst_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1133_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1126_ = v___x_1123_;
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1123_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___f_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__0), 2, 1);
lean_closure_set(v___f_1128_, 0, v_data_1121_);
v___x_1129_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1128_, v_a_1124_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1129_);
v___x_1131_ = v___x_1126_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
else
{
lean_dec(v_data_1121_);
return v___x_1123_;
}
}
case 11:
{
lean_object* v_typeName_1134_; lean_object* v_idx_1135_; lean_object* v_struct_1136_; lean_object* v___x_1137_; 
v_typeName_1134_ = lean_ctor_get(v_e_916_, 0);
lean_inc(v_typeName_1134_);
v_idx_1135_ = lean_ctor_get(v_e_916_, 1);
lean_inc(v_idx_1135_);
v_struct_1136_ = lean_ctor_get(v_e_916_, 2);
lean_inc_ref(v_struct_1136_);
lean_dec_ref_known(v_e_916_, 3);
v___x_1137_ = l_Lean_Elab_Tactic_Do_countUses(v_struct_1136_, v_subst_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1147_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1147_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1147_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___f_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___f_1142_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__1), 3, 2);
lean_closure_set(v___f_1142_, 0, v_typeName_1134_);
lean_closure_set(v___f_1142_, 1, v_idx_1135_);
v___x_1143_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1142_, v_a_1138_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1143_);
v___x_1145_ = v___x_1140_;
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
else
{
lean_dec(v_idx_1135_);
lean_dec(v_typeName_1134_);
return v___x_1137_;
}
}
default: 
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec_ref(v_subst_917_);
v___x_1148_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1149_, 0, v_e_916_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl(lean_object* v_fvarId_1151_, lean_object* v_ty_1152_, lean_object* v_val_x3f_1153_, lean_object* v_bodyUses_1154_, lean_object* v_subst_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v___x_1161_; 
lean_inc_ref(v_subst_1155_);
v___x_1161_ = l_Lean_Elab_Tactic_Do_countUses(v_ty_1152_, v_subst_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1217_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1217_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1217_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v_fst_1166_; lean_object* v_snd_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1216_; 
v_fst_1166_ = lean_ctor_get(v_a_1162_, 0);
v_snd_1167_ = lean_ctor_get(v_a_1162_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_a_1162_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1169_ = v_a_1162_;
v_isShared_1170_ = v_isSharedCheck_1216_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_snd_1167_);
lean_inc(v_fst_1166_);
lean_dec(v_a_1162_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1216_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
uint8_t v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v_fst_1189_; lean_object* v_snd_1190_; 
if (lean_obj_tag(v_val_x3f_1153_) == 0)
{
lean_object* v___x_1200_; 
lean_dec_ref(v_subst_1155_);
v___x_1200_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v_fst_1189_ = v_val_x3f_1153_;
v_snd_1190_ = v___x_1200_;
goto v___jp_1188_;
}
else
{
lean_object* v_val_1201_; lean_object* v___x_1202_; 
v_val_1201_ = lean_ctor_get(v_val_x3f_1153_, 0);
lean_inc(v_val_1201_);
lean_dec_ref_known(v_val_x3f_1153_, 1);
v___x_1202_ = l_Lean_Elab_Tactic_Do_countUses(v_val_1201_, v_subst_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___f_1204_; lean_object* v___x_1205_; lean_object* v_fst_1206_; lean_object* v_snd_1207_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v___f_1204_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4));
v___x_1205_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1204_, v_a_1203_);
v_fst_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_fst_1206_);
v_snd_1207_ = lean_ctor_get(v___x_1205_, 1);
lean_inc(v_snd_1207_);
lean_dec_ref(v___x_1205_);
v_fst_1189_ = v_fst_1206_;
v_snd_1190_ = v_snd_1207_;
goto v___jp_1188_;
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_del_object(v___x_1169_);
lean_dec(v_snd_1167_);
lean_dec(v_fst_1166_);
lean_del_object(v___x_1164_);
lean_dec_ref(v_bodyUses_1154_);
v_a_1208_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1202_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1202_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
v___jp_1171_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1175_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___y_1174_, v_fvarId_1151_);
v___x_1176_ = lean_box(0);
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_1178_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v___y_1172_);
v___x_1179_ = l_Lean_KVMap_setNat(v___x_1176_, v___x_1177_, v___x_1178_);
v___x_1180_ = l_Lean_Elab_Tactic_Do_addMData(v___x_1179_, v_fst_1166_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1175_);
lean_ctor_set(v___x_1169_, 0, v___y_1173_);
v___x_1182_ = v___x_1169_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___y_1173_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v___x_1175_);
v___x_1182_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1180_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1183_);
v___x_1185_ = v___x_1164_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
v___jp_1188_:
{
uint8_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; uint8_t v___x_1195_; 
v___x_1191_ = 0;
v___x_1192_ = lean_box(v___x_1191_);
v___x_1193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_bodyUses_1154_, v_fvarId_1151_, v___x_1192_);
lean_dec(v___x_1192_);
v___x_1194_ = lean_unbox(v___x_1193_);
v___x_1195_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v___x_1194_, v___x_1191_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1196_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_bodyUses_1154_, v_snd_1167_);
lean_dec_ref(v_bodyUses_1154_);
v___x_1197_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v___x_1196_, v_snd_1190_);
lean_dec_ref(v___x_1196_);
v___x_1198_ = lean_unbox(v___x_1193_);
lean_dec(v___x_1193_);
v___y_1172_ = v___x_1198_;
v___y_1173_ = v_fst_1189_;
v___y_1174_ = v___x_1197_;
goto v___jp_1171_;
}
else
{
uint8_t v___x_1199_; 
lean_dec_ref(v_snd_1190_);
lean_dec(v_snd_1167_);
v___x_1199_ = lean_unbox(v___x_1193_);
lean_dec(v___x_1193_);
v___y_1172_ = v___x_1199_;
v___y_1173_ = v_fst_1189_;
v___y_1174_ = v_bodyUses_1154_;
goto v___jp_1171_;
}
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec_ref(v_subst_1155_);
lean_dec_ref(v_bodyUses_1154_);
lean_dec(v_val_x3f_1153_);
v_a_1218_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1161_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1161_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___boxed(lean_object* v_fvarId_1226_, lean_object* v_ty_1227_, lean_object* v_val_x3f_1228_, lean_object* v_bodyUses_1229_, lean_object* v_subst_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_fvarId_1226_, v_ty_1227_, v_val_x3f_1228_, v_bodyUses_1229_, v_subst_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_fvarId_1226_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___boxed(lean_object* v_e_1237_, lean_object* v_subst_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_Elab_Tactic_Do_countUses(v_e_1237_, v_subst_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(lean_object* v_00_u03b2_1245_, lean_object* v_m_1246_, lean_object* v_a_1247_, lean_object* v_fallback_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_1246_, v_a_1247_, v_fallback_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(lean_object* v_00_u03b2_1250_, lean_object* v_m_1251_, lean_object* v_a_1252_, lean_object* v_fallback_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(v_00_u03b2_1250_, v_m_1251_, v_a_1252_, v_fallback_1253_);
lean_dec(v_fallback_1253_);
lean_dec(v_a_1252_);
lean_dec_ref(v_m_1251_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(lean_object* v_00_u03b2_1255_, lean_object* v_m_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_1256_, v_a_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(lean_object* v_00_u03b2_1259_, lean_object* v_m_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(v_00_u03b2_1259_, v_m_1260_, v_a_1261_);
lean_dec(v_a_1261_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(lean_object* v_00_u03b1_1263_, lean_object* v_msg_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___boxed(lean_object* v_00_u03b1_1271_, lean_object* v_msg_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(v_00_u03b1_1271_, v_msg_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4(lean_object* v_00_u03b2_1279_, lean_object* v_m_1280_, lean_object* v_a_1281_, lean_object* v_b_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4___redArg(v_m_1280_, v_a_1281_, v_b_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___redArg(v___y_1287_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9___boxed(lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__5_spec__9(v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(lean_object* v_00_u03b2_1296_, lean_object* v_a_1297_, lean_object* v_fallback_1298_, lean_object* v_x_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_a_1297_, v_fallback_1298_, v_x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1301_, lean_object* v_a_1302_, lean_object* v_fallback_1303_, lean_object* v_x_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(v_00_u03b2_1301_, v_a_1302_, v_fallback_1303_, v_x_1304_);
lean_dec(v_x_1304_);
lean_dec(v_fallback_1303_);
lean_dec(v_a_1302_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(lean_object* v_00_u03b2_1306_, lean_object* v_a_1307_, lean_object* v_x_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_a_1307_, v_x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1310_, lean_object* v_a_1311_, lean_object* v_x_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(v_00_u03b2_1310_, v_a_1311_, v_x_1312_);
lean_dec(v_a_1311_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(lean_object* v_00_u03b2_1314_, lean_object* v_a_1315_, lean_object* v_b_1316_, lean_object* v_x_1317_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v_a_1315_, v_b_1316_, v_x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(lean_object* v_as_1321_, size_t v_i_1322_, size_t v_stop_1323_, lean_object* v_b_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
uint8_t v___x_1330_; 
v___x_1330_ = lean_usize_dec_eq(v_i_1322_, v_stop_1323_);
if (v___x_1330_ == 0)
{
size_t v___x_1331_; size_t v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_sub(v_i_1322_, v___x_1331_);
v___x_1333_ = lean_array_uget_borrowed(v_as_1321_, v___x_1332_);
if (lean_obj_tag(v___x_1333_) == 0)
{
v_i_1322_ = v___x_1332_;
goto _start;
}
else
{
lean_object* v_val_1335_; lean_object* v_fst_1336_; lean_object* v_snd_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_val_1335_ = lean_ctor_get(v___x_1333_, 0);
v_fst_1336_ = lean_ctor_get(v_b_1324_, 0);
lean_inc(v_fst_1336_);
v_snd_1337_ = lean_ctor_get(v_b_1324_, 1);
lean_inc(v_snd_1337_);
lean_dec_ref(v_b_1324_);
v___x_1338_ = l_Lean_LocalDecl_fvarId(v_val_1335_);
v___x_1339_ = l_Lean_LocalDecl_type(v_val_1335_);
v___x_1340_ = l_Lean_LocalDecl_value_x3f(v_val_1335_, v___x_1330_);
v___x_1341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_1342_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v___x_1338_, v___x_1339_, v___x_1340_, v_snd_1337_, v___x_1341_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___x_1338_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v_snd_1344_; lean_object* v_fst_1345_; lean_object* v_fst_1346_; lean_object* v_snd_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1362_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
v_snd_1344_ = lean_ctor_get(v_a_1343_, 1);
lean_inc(v_snd_1344_);
v_fst_1345_ = lean_ctor_get(v_a_1343_, 0);
lean_inc(v_fst_1345_);
lean_dec(v_a_1343_);
v_fst_1346_ = lean_ctor_get(v_snd_1344_, 0);
v_snd_1347_ = lean_ctor_get(v_snd_1344_, 1);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_snd_1344_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1349_ = v_snd_1344_;
v_isShared_1350_ = v_isSharedCheck_1362_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_snd_1347_);
lean_inc(v_fst_1346_);
lean_dec(v_snd_1344_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1362_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___y_1352_; 
if (lean_obj_tag(v_fst_1346_) == 0)
{
lean_object* v___x_1358_; 
lean_inc(v_val_1335_);
v___x_1358_ = l_Lean_LocalDecl_setType(v_val_1335_, v_fst_1345_);
v___y_1352_ = v___x_1358_;
goto v___jp_1351_;
}
else
{
lean_object* v_val_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_val_1359_ = lean_ctor_get(v_fst_1346_, 0);
lean_inc(v_val_1359_);
lean_dec_ref_known(v_fst_1346_, 1);
lean_inc(v_val_1335_);
v___x_1360_ = l_Lean_LocalDecl_setType(v_val_1335_, v_fst_1345_);
v___x_1361_ = l_Lean_LocalDecl_setValue(v___x_1360_, v_val_1359_);
v___y_1352_ = v___x_1361_;
goto v___jp_1351_;
}
v___jp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1353_ = lean_array_push(v_fst_1336_, v___y_1352_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1353_);
v___x_1355_ = v___x_1349_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_snd_1347_);
v___x_1355_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
v_i_1322_ = v___x_1332_;
v_b_1324_ = v___x_1355_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v_fst_1336_);
v_a_1363_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1342_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1342_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
else
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_b_1324_);
return v___x_1371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1372_, lean_object* v_i_1373_, lean_object* v_stop_1374_, lean_object* v_b_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
size_t v_i_boxed_1381_; size_t v_stop_boxed_1382_; lean_object* v_res_1383_; 
v_i_boxed_1381_ = lean_unbox_usize(v_i_1373_);
lean_dec(v_i_1373_);
v_stop_boxed_1382_ = lean_unbox_usize(v_stop_1374_);
lean_dec(v_stop_1374_);
v_res_1383_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_as_1372_, v_i_boxed_1381_, v_stop_boxed_1382_, v_b_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec_ref(v_as_1372_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(lean_object* v_x_1384_, lean_object* v_x_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
if (lean_obj_tag(v_x_1384_) == 0)
{
lean_object* v_cs_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1404_; 
v_cs_1391_ = lean_ctor_get(v_x_1384_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1393_ = v_x_1384_;
v_isShared_1394_ = v_isSharedCheck_1404_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_cs_1391_);
lean_dec(v_x_1384_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1404_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1395_ = lean_array_get_size(v_cs_1391_);
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = lean_nat_dec_lt(v___x_1396_, v___x_1395_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1399_; 
lean_dec_ref(v_cs_1391_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v_x_1385_);
v___x_1399_ = v___x_1393_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_x_1385_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
else
{
size_t v___x_1401_; size_t v___x_1402_; lean_object* v___x_1403_; 
lean_del_object(v___x_1393_);
v___x_1401_ = lean_usize_of_nat(v___x_1395_);
v___x_1402_ = ((size_t)0ULL);
v___x_1403_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_cs_1391_, v___x_1401_, v___x_1402_, v_x_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec_ref(v_cs_1391_);
return v___x_1403_;
}
}
}
else
{
lean_object* v_vs_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1418_; 
v_vs_1405_ = lean_ctor_get(v_x_1384_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1407_ = v_x_1384_;
v_isShared_1408_ = v_isSharedCheck_1418_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_vs_1405_);
lean_dec(v_x_1384_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1418_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1409_ = lean_array_get_size(v_vs_1405_);
v___x_1410_ = lean_unsigned_to_nat(0u);
v___x_1411_ = lean_nat_dec_lt(v___x_1410_, v___x_1409_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1413_; 
lean_dec_ref(v_vs_1405_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set_tag(v___x_1407_, 0);
lean_ctor_set(v___x_1407_, 0, v_x_1385_);
v___x_1413_ = v___x_1407_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_x_1385_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
else
{
size_t v___x_1415_; size_t v___x_1416_; lean_object* v___x_1417_; 
lean_del_object(v___x_1407_);
v___x_1415_ = lean_usize_of_nat(v___x_1409_);
v___x_1416_ = ((size_t)0ULL);
v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_vs_1405_, v___x_1415_, v___x_1416_, v_x_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec_ref(v_vs_1405_);
return v___x_1417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_1419_, size_t v_i_1420_, size_t v_stop_1421_, lean_object* v_b_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
uint8_t v___x_1428_; 
v___x_1428_ = lean_usize_dec_eq(v_i_1420_, v_stop_1421_);
if (v___x_1428_ == 0)
{
size_t v___x_1429_; size_t v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1429_ = ((size_t)1ULL);
v___x_1430_ = lean_usize_sub(v_i_1420_, v___x_1429_);
v___x_1431_ = lean_array_uget_borrowed(v_as_1419_, v___x_1430_);
lean_inc(v___x_1431_);
v___x_1432_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v___x_1431_, v_b_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v_i_1420_ = v___x_1430_;
v_b_1422_ = v_a_1433_;
goto _start;
}
else
{
return v___x_1432_;
}
}
else
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v_b_1422_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_1436_, lean_object* v_i_1437_, lean_object* v_stop_1438_, lean_object* v_b_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
size_t v_i_boxed_1445_; size_t v_stop_boxed_1446_; lean_object* v_res_1447_; 
v_i_boxed_1445_ = lean_unbox_usize(v_i_1437_);
lean_dec(v_i_1437_);
v_stop_boxed_1446_ = lean_unbox_usize(v_stop_1438_);
lean_dec(v_stop_1438_);
v_res_1447_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_as_1436_, v_i_boxed_1445_, v_stop_boxed_1446_, v_b_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec_ref(v_as_1436_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1448_, lean_object* v_x_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_x_1448_, v_x_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(lean_object* v_t_1456_, lean_object* v_init_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_root_1463_; lean_object* v_tail_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v_root_1463_ = lean_ctor_get(v_t_1456_, 0);
lean_inc_ref(v_root_1463_);
v_tail_1464_ = lean_ctor_get(v_t_1456_, 1);
lean_inc_ref(v_tail_1464_);
lean_dec_ref(v_t_1456_);
v___x_1465_ = lean_array_get_size(v_tail_1464_);
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = lean_nat_dec_lt(v___x_1466_, v___x_1465_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; 
lean_dec_ref(v_tail_1464_);
v___x_1468_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1463_, v_init_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
return v___x_1468_;
}
else
{
size_t v___x_1469_; size_t v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = lean_usize_of_nat(v___x_1465_);
v___x_1470_ = ((size_t)0ULL);
v___x_1471_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_tail_1464_, v___x_1469_, v___x_1470_, v_init_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
lean_dec_ref(v_tail_1464_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1473_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
v___x_1473_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1463_, v_a_1472_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
return v___x_1473_;
}
else
{
lean_dec_ref(v_root_1463_);
return v___x_1471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(lean_object* v_t_1474_, lean_object* v_init_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_t_1474_, v_init_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(lean_object* v_lctx_1482_, lean_object* v_init_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_decls_1489_; lean_object* v___x_1490_; 
v_decls_1489_ = lean_ctor_get(v_lctx_1482_, 1);
lean_inc_ref(v_decls_1489_);
lean_dec_ref(v_lctx_1482_);
v___x_1490_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_decls_1489_, v_init_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(lean_object* v_lctx_1491_, lean_object* v_init_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_lctx_1491_, v_init_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(size_t v_sz_1499_, size_t v_i_1500_, lean_object* v_bs_1501_, lean_object* v___y_1502_){
_start:
{
uint8_t v___x_1504_; 
v___x_1504_ = lean_usize_dec_lt(v_i_1500_, v_sz_1499_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_bs_1501_);
return v___x_1505_;
}
else
{
lean_object* v_v_1506_; lean_object* v___x_1507_; lean_object* v_bs_x27_1508_; lean_object* v_a_1510_; 
v_v_1506_ = lean_array_uget(v_bs_1501_, v_i_1500_);
v___x_1507_ = lean_unsigned_to_nat(0u);
v_bs_x27_1508_ = lean_array_uset(v_bs_1501_, v_i_1500_, v___x_1507_);
if (lean_obj_tag(v_v_1506_) == 0)
{
v_a_1510_ = v_v_1506_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1529_; 
v_isSharedCheck_1529_ = !lean_is_exclusive(v_v_1506_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v_v_1506_, 0);
lean_dec(v_unused_1530_);
v___x_1516_ = v_v_1506_;
v_isShared_1517_ = v_isSharedCheck_1529_;
goto v_resetjp_1515_;
}
else
{
lean_dec(v_v_1506_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1529_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1518_ = lean_st_ref_take(v___y_1502_);
v___x_1519_ = l_Lean_instInhabitedLocalDecl_default;
v___x_1520_ = lean_array_get_size(v___x_1518_);
v___x_1521_ = lean_unsigned_to_nat(1u);
v___x_1522_ = lean_nat_sub(v___x_1520_, v___x_1521_);
v___x_1523_ = lean_array_get(v___x_1519_, v___x_1518_, v___x_1522_);
lean_dec(v___x_1522_);
v___x_1524_ = lean_array_pop(v___x_1518_);
v___x_1525_ = lean_st_ref_set(v___y_1502_, v___x_1524_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1523_);
v___x_1527_ = v___x_1516_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1523_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
v_a_1510_ = v___x_1527_;
goto v___jp_1509_;
}
}
}
v___jp_1509_:
{
size_t v___x_1511_; size_t v___x_1512_; lean_object* v___x_1513_; 
v___x_1511_ = ((size_t)1ULL);
v___x_1512_ = lean_usize_add(v_i_1500_, v___x_1511_);
v___x_1513_ = lean_array_uset(v_bs_x27_1508_, v_i_1500_, v_a_1510_);
v_i_1500_ = v___x_1512_;
v_bs_1501_ = v___x_1513_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg___boxed(lean_object* v_sz_1531_, lean_object* v_i_1532_, lean_object* v_bs_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
size_t v_sz_boxed_1536_; size_t v_i_boxed_1537_; lean_object* v_res_1538_; 
v_sz_boxed_1536_ = lean_unbox_usize(v_sz_1531_);
lean_dec(v_sz_1531_);
v_i_boxed_1537_ = lean_unbox_usize(v_i_1532_);
lean_dec(v_i_1532_);
v_res_1538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_boxed_1536_, v_i_boxed_1537_, v_bs_1533_, v___y_1534_);
lean_dec(v___y_1534_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(lean_object* v_x_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
if (lean_obj_tag(v_x_1539_) == 0)
{
lean_object* v_cs_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1572_; 
v_cs_1546_ = lean_ctor_get(v_x_1539_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_x_1539_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1548_ = v_x_1539_;
v_isShared_1549_ = v_isSharedCheck_1572_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_cs_1546_);
lean_dec(v_x_1539_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1572_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
size_t v_sz_1550_; size_t v___x_1551_; lean_object* v___x_1552_; 
v_sz_1550_ = lean_array_size(v_cs_1546_);
v___x_1551_ = ((size_t)0ULL);
v___x_1552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_1550_, v___x_1551_, v_cs_1546_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1563_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1563_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1563_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v_a_1553_);
v___x_1558_ = v___x_1548_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1560_; 
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
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_del_object(v___x_1548_);
v_a_1564_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1552_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1552_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
else
{
lean_object* v_vs_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1599_; 
v_vs_1573_ = lean_ctor_get(v_x_1539_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_x_1539_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1575_ = v_x_1539_;
v_isShared_1576_ = v_isSharedCheck_1599_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_vs_1573_);
lean_dec(v_x_1539_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1599_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
size_t v_sz_1577_; size_t v___x_1578_; lean_object* v___x_1579_; 
v_sz_1577_ = lean_array_size(v_vs_1573_);
v___x_1578_ = ((size_t)0ULL);
v___x_1579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1577_, v___x_1578_, v_vs_1573_, v___y_1540_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1590_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1590_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1590_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v_a_1580_);
v___x_1585_ = v___x_1575_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1587_; 
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1585_);
v___x_1587_ = v___x_1582_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_del_object(v___x_1575_);
v_a_1591_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1579_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1579_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(size_t v_sz_1600_, size_t v_i_1601_, lean_object* v_bs_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
uint8_t v___x_1609_; 
v___x_1609_ = lean_usize_dec_lt(v_i_1601_, v_sz_1600_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1610_, 0, v_bs_1602_);
return v___x_1610_;
}
else
{
lean_object* v_v_1611_; lean_object* v___x_1612_; 
v_v_1611_ = lean_array_uget_borrowed(v_bs_1602_, v_i_1601_);
lean_inc(v_v_1611_);
v___x_1612_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_v_1611_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1614_; lean_object* v_bs_x27_1615_; size_t v___x_1616_; size_t v___x_1617_; lean_object* v___x_1618_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1614_ = lean_unsigned_to_nat(0u);
v_bs_x27_1615_ = lean_array_uset(v_bs_1602_, v_i_1601_, v___x_1614_);
v___x_1616_ = ((size_t)1ULL);
v___x_1617_ = lean_usize_add(v_i_1601_, v___x_1616_);
v___x_1618_ = lean_array_uset(v_bs_x27_1615_, v_i_1601_, v_a_1613_);
v_i_1601_ = v___x_1617_;
v_bs_1602_ = v___x_1618_;
goto _start;
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref(v_bs_1602_);
v_a_1620_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1612_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1612_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_sz_1628_, lean_object* v_i_1629_, lean_object* v_bs_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
size_t v_sz_boxed_1637_; size_t v_i_boxed_1638_; lean_object* v_res_1639_; 
v_sz_boxed_1637_ = lean_unbox_usize(v_sz_1628_);
lean_dec(v_sz_1628_);
v_i_boxed_1638_ = lean_unbox_usize(v_i_1629_);
lean_dec(v_i_1629_);
v_res_1639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_boxed_1637_, v_i_boxed_1638_, v_bs_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(lean_object* v_x_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_x_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(lean_object* v_t_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_root_1655_; lean_object* v_tail_1656_; lean_object* v_size_1657_; size_t v_shift_1658_; lean_object* v_tailOff_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1695_; 
v_root_1655_ = lean_ctor_get(v_t_1648_, 0);
v_tail_1656_ = lean_ctor_get(v_t_1648_, 1);
v_size_1657_ = lean_ctor_get(v_t_1648_, 2);
v_shift_1658_ = lean_ctor_get_usize(v_t_1648_, 4);
v_tailOff_1659_ = lean_ctor_get(v_t_1648_, 3);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_t_1648_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1661_ = v_t_1648_;
v_isShared_1662_ = v_isSharedCheck_1695_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_tailOff_1659_);
lean_inc(v_size_1657_);
lean_inc(v_tail_1656_);
lean_inc(v_root_1655_);
lean_dec(v_t_1648_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1695_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_root_1655_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; size_t v_sz_1665_; size_t v___x_1666_; lean_object* v___x_1667_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
v_sz_1665_ = lean_array_size(v_tail_1656_);
v___x_1666_ = ((size_t)0ULL);
v___x_1667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1665_, v___x_1666_, v_tail_1656_, v___y_1649_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1678_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1678_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1678_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 1, v_a_1668_);
lean_ctor_set(v___x_1661_, 0, v_a_1664_);
v___x_1673_ = v___x_1661_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1664_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_a_1668_);
lean_ctor_set(v_reuseFailAlloc_1677_, 2, v_size_1657_);
lean_ctor_set(v_reuseFailAlloc_1677_, 3, v_tailOff_1659_);
lean_ctor_set_usize(v_reuseFailAlloc_1677_, 4, v_shift_1658_);
v___x_1673_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1675_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1673_);
v___x_1675_ = v___x_1670_;
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
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec(v_a_1664_);
lean_del_object(v___x_1661_);
lean_dec(v_tailOff_1659_);
lean_dec(v_size_1657_);
v_a_1679_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1667_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1667_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_del_object(v___x_1661_);
lean_dec(v_tailOff_1659_);
lean_dec(v_size_1657_);
lean_dec_ref(v_tail_1656_);
v_a_1687_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1663_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1663_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1___boxed(lean_object* v_t_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_t_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx(lean_object* v_ctx_1704_, lean_object* v_targetUses_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v_decls_1711_; lean_object* v_fvarIdToDecl_1712_; lean_object* v_auxDeclToFullName_1713_; lean_object* v_size_1714_; lean_object* v_decls_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v_decls_1711_ = lean_ctor_get(v_ctx_1704_, 1);
lean_inc_ref(v_decls_1711_);
v_fvarIdToDecl_1712_ = lean_ctor_get(v_ctx_1704_, 0);
lean_inc_ref(v_fvarIdToDecl_1712_);
v_auxDeclToFullName_1713_ = lean_ctor_get(v_ctx_1704_, 2);
lean_inc(v_auxDeclToFullName_1713_);
v_size_1714_ = lean_ctor_get(v_decls_1711_, 2);
v_decls_1715_ = lean_mk_empty_array_with_capacity(v_size_1714_);
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v_decls_1715_);
lean_ctor_set(v___x_1716_, 1, v_targetUses_1705_);
v___x_1717_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_ctx_1704_, v___x_1716_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v_fst_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v_fst_1719_ = lean_ctor_get(v_a_1718_, 0);
lean_inc(v_fst_1719_);
lean_dec(v_a_1718_);
v___x_1720_ = lean_st_mk_ref(v_fst_1719_);
v___x_1721_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_decls_1711_, v___x_1720_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1731_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1726_ = lean_st_ref_get(v___x_1720_);
lean_dec(v___x_1720_);
lean_dec(v___x_1726_);
v___x_1727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1727_, 0, v_fvarIdToDecl_1712_);
lean_ctor_set(v___x_1727_, 1, v_a_1722_);
lean_ctor_set(v___x_1727_, 2, v_auxDeclToFullName_1713_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1727_);
v___x_1729_ = v___x_1724_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec(v___x_1720_);
lean_dec(v_auxDeclToFullName_1713_);
lean_dec_ref(v_fvarIdToDecl_1712_);
v_a_1732_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1721_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1721_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec(v_auxDeclToFullName_1713_);
lean_dec_ref(v_fvarIdToDecl_1712_);
lean_dec_ref(v_decls_1711_);
v_a_1740_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1717_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1717_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx___boxed(lean_object* v_ctx_1748_, lean_object* v_targetUses_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_ctx_1748_, v_targetUses_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(size_t v_sz_1756_, size_t v_i_1757_, lean_object* v_bs_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1756_, v_i_1757_, v_bs_1758_, v___y_1759_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(lean_object* v_sz_1766_, lean_object* v_i_1767_, lean_object* v_bs_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
size_t v_sz_boxed_1775_; size_t v_i_boxed_1776_; lean_object* v_res_1777_; 
v_sz_boxed_1775_ = lean_unbox_usize(v_sz_1766_);
lean_dec(v_sz_1766_);
v_i_boxed_1776_ = lean_unbox_usize(v_i_1767_);
lean_dec(v_i_1767_);
v_res_1777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(v_sz_boxed_1775_, v_i_boxed_1776_, v_bs_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
return v_res_1777_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_doNotDup(uint8_t v_u_1778_, lean_object* v_rhs_1779_, uint8_t v_elimTrivial_1780_){
_start:
{
uint8_t v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = 2;
v___x_1782_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_u_1778_, v___x_1781_);
if (v___x_1782_ == 0)
{
return v___x_1782_;
}
else
{
if (v_elimTrivial_1780_ == 0)
{
uint8_t v___x_1783_; 
v___x_1783_ = lean_bool_not(v_elimTrivial_1780_);
return v___x_1783_;
}
else
{
uint8_t v___x_1784_; uint8_t v___x_1785_; 
v___x_1784_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_rhs_1779_);
v___x_1785_ = lean_bool_not(v___x_1784_);
return v___x_1785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_doNotDup___boxed(lean_object* v_u_1786_, lean_object* v_rhs_1787_, lean_object* v_elimTrivial_1788_){
_start:
{
uint8_t v_u_boxed_1789_; uint8_t v_elimTrivial_boxed_1790_; uint8_t v_res_1791_; lean_object* v_r_1792_; 
v_u_boxed_1789_ = lean_unbox(v_u_1786_);
v_elimTrivial_boxed_1790_ = lean_unbox(v_elimTrivial_1788_);
v_res_1791_ = l_Lean_Elab_Tactic_Do_doNotDup(v_u_boxed_1789_, v_rhs_1787_, v_elimTrivial_boxed_1790_);
lean_dec_ref(v_rhs_1787_);
v_r_1792_ = lean_box(v_res_1791_);
return v_r_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(uint8_t v_elimTrivial_1795_, lean_object* v_e_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
if (lean_obj_tag(v_e_1796_) == 8)
{
lean_object* v_type_1803_; 
v_type_1803_ = lean_ctor_get(v_e_1796_, 1);
if (lean_obj_tag(v_type_1803_) == 10)
{
lean_object* v_value_1804_; lean_object* v_body_1805_; lean_object* v_data_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v_uses_1810_; uint8_t v___x_1811_; 
v_value_1804_ = lean_ctor_get(v_e_1796_, 2);
v_body_1805_ = lean_ctor_get(v_e_1796_, 3);
v_data_1806_ = lean_ctor_get(v_type_1803_, 0);
v___x_1807_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_1808_ = lean_unsigned_to_nat(2u);
v___x_1809_ = l_Lean_KVMap_getNat(v_data_1806_, v___x_1807_, v___x_1808_);
v_uses_1810_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_1809_);
lean_dec(v___x_1809_);
v___x_1811_ = l_Lean_Elab_Tactic_Do_doNotDup(v_uses_1810_, v_value_1804_, v_elimTrivial_1795_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = lean_expr_instantiate1(v_body_1805_, v_value_1804_);
v___x_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
return v___x_1814_;
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
return v___x_1820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(lean_object* v_elimTrivial_1821_, lean_object* v_e_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
uint8_t v_elimTrivial_boxed_1829_; lean_object* v_res_1830_; 
v_elimTrivial_boxed_1829_ = lean_unbox(v_elimTrivial_1821_);
v_res_1830_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(v_elimTrivial_boxed_1829_, v_e_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v_e_1822_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(lean_object* v_e_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v_e_1831_);
v___x_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(lean_object* v_e_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(v_e_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
return v_res_1847_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = l_Lean_maxRecDepthErrorMessage;
v___x_1854_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
return v___x_1854_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_1856_ = l_Lean_MessageData_ofFormat(v___x_1855_);
return v___x_1856_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_1858_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_1859_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v___x_1857_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_1860_){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1862_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v_ref_1860_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1865_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(lean_object* v_x_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v___y_1877_; lean_object* v_fileName_1886_; lean_object* v_fileMap_1887_; lean_object* v_options_1888_; lean_object* v_currRecDepth_1889_; lean_object* v_maxRecDepth_1890_; lean_object* v_ref_1891_; lean_object* v_currNamespace_1892_; lean_object* v_openDecls_1893_; lean_object* v_initHeartbeats_1894_; lean_object* v_maxHeartbeats_1895_; lean_object* v_quotContext_1896_; lean_object* v_currMacroScope_1897_; uint8_t v_diag_1898_; lean_object* v_cancelTk_x3f_1899_; uint8_t v_suppressElabErrors_1900_; lean_object* v_inheritedTraceOptions_1901_; uint8_t v___y_1903_; lean_object* v___x_1909_; uint8_t v___x_1910_; uint8_t v___x_1911_; 
v_fileName_1886_ = lean_ctor_get(v___y_1873_, 0);
v_fileMap_1887_ = lean_ctor_get(v___y_1873_, 1);
v_options_1888_ = lean_ctor_get(v___y_1873_, 2);
v_currRecDepth_1889_ = lean_ctor_get(v___y_1873_, 3);
v_maxRecDepth_1890_ = lean_ctor_get(v___y_1873_, 4);
v_ref_1891_ = lean_ctor_get(v___y_1873_, 5);
v_currNamespace_1892_ = lean_ctor_get(v___y_1873_, 6);
v_openDecls_1893_ = lean_ctor_get(v___y_1873_, 7);
v_initHeartbeats_1894_ = lean_ctor_get(v___y_1873_, 8);
v_maxHeartbeats_1895_ = lean_ctor_get(v___y_1873_, 9);
v_quotContext_1896_ = lean_ctor_get(v___y_1873_, 10);
v_currMacroScope_1897_ = lean_ctor_get(v___y_1873_, 11);
v_diag_1898_ = lean_ctor_get_uint8(v___y_1873_, sizeof(void*)*14);
v_cancelTk_x3f_1899_ = lean_ctor_get(v___y_1873_, 12);
v_suppressElabErrors_1900_ = lean_ctor_get_uint8(v___y_1873_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1901_ = lean_ctor_get(v___y_1873_, 13);
v___x_1909_ = lean_unsigned_to_nat(0u);
v___x_1910_ = lean_nat_dec_eq(v_maxRecDepth_1890_, v___x_1909_);
v___x_1911_ = lean_bool_not(v___x_1910_);
if (v___x_1911_ == 0)
{
v___y_1903_ = v___x_1911_;
goto v___jp_1902_;
}
else
{
uint8_t v___x_1912_; 
v___x_1912_ = lean_nat_dec_eq(v_currRecDepth_1889_, v_maxRecDepth_1890_);
v___y_1903_ = v___x_1912_;
goto v___jp_1902_;
}
v___jp_1876_:
{
if (lean_obj_tag(v___y_1877_) == 0)
{
return v___y_1877_;
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
v_a_1878_ = lean_ctor_get(v___y_1877_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___y_1877_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___y_1877_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___y_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
v___jp_1902_:
{
if (v___y_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1904_ = lean_unsigned_to_nat(1u);
v___x_1905_ = lean_nat_add(v_currRecDepth_1889_, v___x_1904_);
lean_inc_ref(v_inheritedTraceOptions_1901_);
lean_inc(v_cancelTk_x3f_1899_);
lean_inc(v_currMacroScope_1897_);
lean_inc(v_quotContext_1896_);
lean_inc(v_maxHeartbeats_1895_);
lean_inc(v_initHeartbeats_1894_);
lean_inc(v_openDecls_1893_);
lean_inc(v_currNamespace_1892_);
lean_inc(v_ref_1891_);
lean_inc(v_maxRecDepth_1890_);
lean_inc_ref(v_options_1888_);
lean_inc_ref(v_fileMap_1887_);
lean_inc_ref(v_fileName_1886_);
v___x_1906_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1906_, 0, v_fileName_1886_);
lean_ctor_set(v___x_1906_, 1, v_fileMap_1887_);
lean_ctor_set(v___x_1906_, 2, v_options_1888_);
lean_ctor_set(v___x_1906_, 3, v___x_1905_);
lean_ctor_set(v___x_1906_, 4, v_maxRecDepth_1890_);
lean_ctor_set(v___x_1906_, 5, v_ref_1891_);
lean_ctor_set(v___x_1906_, 6, v_currNamespace_1892_);
lean_ctor_set(v___x_1906_, 7, v_openDecls_1893_);
lean_ctor_set(v___x_1906_, 8, v_initHeartbeats_1894_);
lean_ctor_set(v___x_1906_, 9, v_maxHeartbeats_1895_);
lean_ctor_set(v___x_1906_, 10, v_quotContext_1896_);
lean_ctor_set(v___x_1906_, 11, v_currMacroScope_1897_);
lean_ctor_set(v___x_1906_, 12, v_cancelTk_x3f_1899_);
lean_ctor_set(v___x_1906_, 13, v_inheritedTraceOptions_1901_);
lean_ctor_set_uint8(v___x_1906_, sizeof(void*)*14, v_diag_1898_);
lean_ctor_set_uint8(v___x_1906_, sizeof(void*)*14 + 1, v_suppressElabErrors_1900_);
lean_inc(v___y_1874_);
lean_inc(v___y_1872_);
lean_inc_ref(v___y_1871_);
lean_inc(v___y_1870_);
lean_inc(v___y_1869_);
v___x_1907_ = lean_apply_7(v_x_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___x_1906_, v___y_1874_, lean_box(0));
v___y_1877_ = v___x_1907_;
goto v___jp_1876_;
}
else
{
lean_object* v___x_1908_; 
lean_dec_ref(v_x_1868_);
lean_inc(v_ref_1891_);
v___x_1908_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1891_);
v___y_1877_ = v___x_1908_;
goto v___jp_1876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec(v___y_1914_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_a_1922_, lean_object* v_x_1923_){
_start:
{
if (lean_obj_tag(v_x_1923_) == 0)
{
lean_object* v___x_1924_; 
v___x_1924_ = lean_box(0);
return v___x_1924_;
}
else
{
lean_object* v_key_1925_; lean_object* v_value_1926_; lean_object* v_tail_1927_; uint8_t v___x_1928_; 
v_key_1925_ = lean_ctor_get(v_x_1923_, 0);
v_value_1926_ = lean_ctor_get(v_x_1923_, 1);
v_tail_1927_ = lean_ctor_get(v_x_1923_, 2);
v___x_1928_ = l_Lean_ExprStructEq_beq(v_key_1925_, v_a_1922_);
if (v___x_1928_ == 0)
{
v_x_1923_ = v_tail_1927_;
goto _start;
}
else
{
lean_object* v___x_1930_; 
lean_inc(v_value_1926_);
v___x_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1930_, 0, v_value_1926_);
return v___x_1930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_a_1931_, lean_object* v_x_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1931_, v_x_1932_);
lean_dec(v_x_1932_);
lean_dec_ref(v_a_1931_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object* v_m_1934_, lean_object* v_a_1935_){
_start:
{
lean_object* v_buckets_1936_; lean_object* v___x_1937_; uint64_t v___x_1938_; uint64_t v___x_1939_; uint64_t v___x_1940_; uint64_t v_fold_1941_; uint64_t v___x_1942_; uint64_t v___x_1943_; uint64_t v___x_1944_; size_t v___x_1945_; size_t v___x_1946_; size_t v___x_1947_; size_t v___x_1948_; size_t v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v_buckets_1936_ = lean_ctor_get(v_m_1934_, 1);
v___x_1937_ = lean_array_get_size(v_buckets_1936_);
v___x_1938_ = l_Lean_ExprStructEq_hash(v_a_1935_);
v___x_1939_ = 32ULL;
v___x_1940_ = lean_uint64_shift_right(v___x_1938_, v___x_1939_);
v_fold_1941_ = lean_uint64_xor(v___x_1938_, v___x_1940_);
v___x_1942_ = 16ULL;
v___x_1943_ = lean_uint64_shift_right(v_fold_1941_, v___x_1942_);
v___x_1944_ = lean_uint64_xor(v_fold_1941_, v___x_1943_);
v___x_1945_ = lean_uint64_to_usize(v___x_1944_);
v___x_1946_ = lean_usize_of_nat(v___x_1937_);
v___x_1947_ = ((size_t)1ULL);
v___x_1948_ = lean_usize_sub(v___x_1946_, v___x_1947_);
v___x_1949_ = lean_usize_land(v___x_1945_, v___x_1948_);
v___x_1950_ = lean_array_uget_borrowed(v_buckets_1936_, v___x_1949_);
v___x_1951_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_1935_, v___x_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_1952_, v_a_1953_);
lean_dec_ref(v_a_1953_);
lean_dec_ref(v_m_1952_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v_b_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; 
lean_inc(v___y_1962_);
lean_inc_ref(v___y_1961_);
lean_inc(v___y_1960_);
lean_inc_ref(v___y_1959_);
lean_inc(v___y_1957_);
lean_inc(v___y_1956_);
v___x_1964_ = lean_apply_8(v_k_1955_, v_b_1958_, v___y_1956_, v___y_1957_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, lean_box(0));
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v_b_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_1965_, v___y_1966_, v___y_1967_, v_b_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1967_);
lean_dec(v___y_1966_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_1975_, lean_object* v_type_1976_, lean_object* v_val_1977_, lean_object* v_k_1978_, uint8_t v_nondep_1979_, uint8_t v_kind_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___f_1988_; lean_object* v___x_1989_; 
lean_inc(v___y_1982_);
lean_inc(v___y_1981_);
v___f_1988_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1988_, 0, v_k_1978_);
lean_closure_set(v___f_1988_, 1, v___y_1981_);
lean_closure_set(v___f_1988_, 2, v___y_1982_);
v___x_1989_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1975_, v_type_1976_, v_val_1977_, v___f_1988_, v_nondep_1979_, v_kind_1980_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
if (lean_obj_tag(v___x_1989_) == 0)
{
return v___x_1989_;
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_1998_, lean_object* v_type_1999_, lean_object* v_val_2000_, lean_object* v_k_2001_, lean_object* v_nondep_2002_, lean_object* v_kind_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
uint8_t v_nondep_boxed_2011_; uint8_t v_kind_boxed_2012_; lean_object* v_res_2013_; 
v_nondep_boxed_2011_ = lean_unbox(v_nondep_2002_);
v_kind_boxed_2012_ = lean_unbox(v_kind_2003_);
v_res_2013_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_1998_, v_type_1999_, v_val_2000_, v_k_2001_, v_nondep_boxed_2011_, v_kind_boxed_2012_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec(v___y_2004_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_2014_, uint8_t v_bi_2015_, lean_object* v_type_2016_, lean_object* v_k_2017_, uint8_t v_kind_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___f_2026_; lean_object* v___x_2027_; 
lean_inc(v___y_2020_);
lean_inc(v___y_2019_);
v___f_2026_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2026_, 0, v_k_2017_);
lean_closure_set(v___f_2026_, 1, v___y_2019_);
lean_closure_set(v___f_2026_, 2, v___y_2020_);
v___x_2027_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2014_, v_bi_2015_, v_type_2016_, v___f_2026_, v_kind_2018_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2027_) == 0)
{
return v___x_2027_;
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_2036_, lean_object* v_bi_2037_, lean_object* v_type_2038_, lean_object* v_k_2039_, lean_object* v_kind_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
uint8_t v_bi_boxed_2048_; uint8_t v_kind_boxed_2049_; lean_object* v_res_2050_; 
v_bi_boxed_2048_ = lean_unbox(v_bi_2037_);
v_kind_boxed_2049_ = lean_unbox(v_kind_2040_);
v_res_2050_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_2036_, v_bi_boxed_2048_, v_type_2038_, v_k_2039_, v_kind_boxed_2049_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec(v___y_2041_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2051_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(v___x_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2067_, lean_object* v_x_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = lean_apply_1(v_x_2068_, lean_box(0));
v___x_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2077_, lean_object* v_x_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(v_00_u03b1_2077_, v_x_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(lean_object* v_x_2086_, lean_object* v_x_2087_){
_start:
{
if (lean_obj_tag(v_x_2087_) == 0)
{
return v_x_2086_;
}
else
{
lean_object* v_key_2088_; lean_object* v_value_2089_; lean_object* v_tail_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2113_; 
v_key_2088_ = lean_ctor_get(v_x_2087_, 0);
v_value_2089_ = lean_ctor_get(v_x_2087_, 1);
v_tail_2090_ = lean_ctor_get(v_x_2087_, 2);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_x_2087_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2092_ = v_x_2087_;
v_isShared_2093_ = v_isSharedCheck_2113_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_tail_2090_);
lean_inc(v_value_2089_);
lean_inc(v_key_2088_);
lean_dec(v_x_2087_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2113_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; uint64_t v___x_2095_; uint64_t v___x_2096_; uint64_t v___x_2097_; uint64_t v_fold_2098_; uint64_t v___x_2099_; uint64_t v___x_2100_; uint64_t v___x_2101_; size_t v___x_2102_; size_t v___x_2103_; size_t v___x_2104_; size_t v___x_2105_; size_t v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2094_ = lean_array_get_size(v_x_2086_);
v___x_2095_ = l_Lean_ExprStructEq_hash(v_key_2088_);
v___x_2096_ = 32ULL;
v___x_2097_ = lean_uint64_shift_right(v___x_2095_, v___x_2096_);
v_fold_2098_ = lean_uint64_xor(v___x_2095_, v___x_2097_);
v___x_2099_ = 16ULL;
v___x_2100_ = lean_uint64_shift_right(v_fold_2098_, v___x_2099_);
v___x_2101_ = lean_uint64_xor(v_fold_2098_, v___x_2100_);
v___x_2102_ = lean_uint64_to_usize(v___x_2101_);
v___x_2103_ = lean_usize_of_nat(v___x_2094_);
v___x_2104_ = ((size_t)1ULL);
v___x_2105_ = lean_usize_sub(v___x_2103_, v___x_2104_);
v___x_2106_ = lean_usize_land(v___x_2102_, v___x_2105_);
v___x_2107_ = lean_array_uget_borrowed(v_x_2086_, v___x_2106_);
lean_inc(v___x_2107_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 2, v___x_2107_);
v___x_2109_ = v___x_2092_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_key_2088_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_value_2089_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2110_; 
v___x_2110_ = lean_array_uset(v_x_2086_, v___x_2106_, v___x_2109_);
v_x_2086_ = v___x_2110_;
v_x_2087_ = v_tail_2090_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(lean_object* v_i_2114_, lean_object* v_source_2115_, lean_object* v_target_2116_){
_start:
{
lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2117_ = lean_array_get_size(v_source_2115_);
v___x_2118_ = lean_nat_dec_lt(v_i_2114_, v___x_2117_);
if (v___x_2118_ == 0)
{
lean_dec_ref(v_source_2115_);
lean_dec(v_i_2114_);
return v_target_2116_;
}
else
{
lean_object* v_es_2119_; lean_object* v___x_2120_; lean_object* v_source_2121_; lean_object* v_target_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v_es_2119_ = lean_array_fget(v_source_2115_, v_i_2114_);
v___x_2120_ = lean_box(0);
v_source_2121_ = lean_array_fset(v_source_2115_, v_i_2114_, v___x_2120_);
v_target_2122_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_target_2116_, v_es_2119_);
v___x_2123_ = lean_unsigned_to_nat(1u);
v___x_2124_ = lean_nat_add(v_i_2114_, v___x_2123_);
lean_dec(v_i_2114_);
v_i_2114_ = v___x_2124_;
v_source_2115_ = v_source_2121_;
v_target_2116_ = v_target_2122_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(lean_object* v_data_2126_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v_nbuckets_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2127_ = lean_array_get_size(v_data_2126_);
v___x_2128_ = lean_unsigned_to_nat(2u);
v_nbuckets_2129_ = lean_nat_mul(v___x_2127_, v___x_2128_);
v___x_2130_ = lean_unsigned_to_nat(0u);
v___x_2131_ = lean_box(0);
v___x_2132_ = lean_mk_array(v_nbuckets_2129_, v___x_2131_);
v___x_2133_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v___x_2130_, v_data_2126_, v___x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(lean_object* v_a_2134_, lean_object* v_b_2135_, lean_object* v_x_2136_){
_start:
{
if (lean_obj_tag(v_x_2136_) == 0)
{
lean_dec(v_b_2135_);
lean_dec_ref(v_a_2134_);
return v_x_2136_;
}
else
{
lean_object* v_key_2137_; lean_object* v_value_2138_; lean_object* v_tail_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2151_; 
v_key_2137_ = lean_ctor_get(v_x_2136_, 0);
v_value_2138_ = lean_ctor_get(v_x_2136_, 1);
v_tail_2139_ = lean_ctor_get(v_x_2136_, 2);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_x_2136_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2141_ = v_x_2136_;
v_isShared_2142_ = v_isSharedCheck_2151_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_tail_2139_);
lean_inc(v_value_2138_);
lean_inc(v_key_2137_);
lean_dec(v_x_2136_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2151_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
uint8_t v___x_2143_; 
v___x_2143_ = l_Lean_ExprStructEq_beq(v_key_2137_, v_a_2134_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; lean_object* v___x_2146_; 
v___x_2144_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2134_, v_b_2135_, v_tail_2139_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 2, v___x_2144_);
v___x_2146_ = v___x_2141_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_key_2137_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_value_2138_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
else
{
lean_object* v___x_2149_; 
lean_dec(v_value_2138_);
lean_dec(v_key_2137_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 1, v_b_2135_);
lean_ctor_set(v___x_2141_, 0, v_a_2134_);
v___x_2149_ = v___x_2141_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2134_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v_b_2135_);
lean_ctor_set(v_reuseFailAlloc_2150_, 2, v_tail_2139_);
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
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_a_2152_, lean_object* v_x_2153_){
_start:
{
if (lean_obj_tag(v_x_2153_) == 0)
{
uint8_t v___x_2154_; 
v___x_2154_ = 0;
return v___x_2154_;
}
else
{
lean_object* v_key_2155_; lean_object* v_tail_2156_; uint8_t v___x_2157_; 
v_key_2155_ = lean_ctor_get(v_x_2153_, 0);
v_tail_2156_ = lean_ctor_get(v_x_2153_, 2);
v___x_2157_ = l_Lean_ExprStructEq_beq(v_key_2155_, v_a_2152_);
if (v___x_2157_ == 0)
{
v_x_2153_ = v_tail_2156_;
goto _start;
}
else
{
return v___x_2157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_a_2159_, lean_object* v_x_2160_){
_start:
{
uint8_t v_res_2161_; lean_object* v_r_2162_; 
v_res_2161_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2159_, v_x_2160_);
lean_dec(v_x_2160_);
lean_dec_ref(v_a_2159_);
v_r_2162_ = lean_box(v_res_2161_);
return v_r_2162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object* v_m_2163_, lean_object* v_a_2164_, lean_object* v_b_2165_){
_start:
{
lean_object* v_size_2166_; lean_object* v_buckets_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2210_; 
v_size_2166_ = lean_ctor_get(v_m_2163_, 0);
v_buckets_2167_ = lean_ctor_get(v_m_2163_, 1);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_m_2163_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2169_ = v_m_2163_;
v_isShared_2170_ = v_isSharedCheck_2210_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_buckets_2167_);
lean_inc(v_size_2166_);
lean_dec(v_m_2163_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2210_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; uint64_t v___x_2172_; uint64_t v___x_2173_; uint64_t v___x_2174_; uint64_t v_fold_2175_; uint64_t v___x_2176_; uint64_t v___x_2177_; uint64_t v___x_2178_; size_t v___x_2179_; size_t v___x_2180_; size_t v___x_2181_; size_t v___x_2182_; size_t v___x_2183_; lean_object* v_bkt_2184_; uint8_t v___x_2185_; 
v___x_2171_ = lean_array_get_size(v_buckets_2167_);
v___x_2172_ = l_Lean_ExprStructEq_hash(v_a_2164_);
v___x_2173_ = 32ULL;
v___x_2174_ = lean_uint64_shift_right(v___x_2172_, v___x_2173_);
v_fold_2175_ = lean_uint64_xor(v___x_2172_, v___x_2174_);
v___x_2176_ = 16ULL;
v___x_2177_ = lean_uint64_shift_right(v_fold_2175_, v___x_2176_);
v___x_2178_ = lean_uint64_xor(v_fold_2175_, v___x_2177_);
v___x_2179_ = lean_uint64_to_usize(v___x_2178_);
v___x_2180_ = lean_usize_of_nat(v___x_2171_);
v___x_2181_ = ((size_t)1ULL);
v___x_2182_ = lean_usize_sub(v___x_2180_, v___x_2181_);
v___x_2183_ = lean_usize_land(v___x_2179_, v___x_2182_);
v_bkt_2184_ = lean_array_uget_borrowed(v_buckets_2167_, v___x_2183_);
v___x_2185_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_2164_, v_bkt_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v_size_x27_2187_; lean_object* v___x_2188_; lean_object* v_buckets_x27_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2186_ = lean_unsigned_to_nat(1u);
v_size_x27_2187_ = lean_nat_add(v_size_2166_, v___x_2186_);
lean_dec(v_size_2166_);
lean_inc(v_bkt_2184_);
v___x_2188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2188_, 0, v_a_2164_);
lean_ctor_set(v___x_2188_, 1, v_b_2165_);
lean_ctor_set(v___x_2188_, 2, v_bkt_2184_);
v_buckets_x27_2189_ = lean_array_uset(v_buckets_2167_, v___x_2183_, v___x_2188_);
v___x_2190_ = lean_unsigned_to_nat(4u);
v___x_2191_ = lean_nat_mul(v_size_x27_2187_, v___x_2190_);
v___x_2192_ = lean_unsigned_to_nat(3u);
v___x_2193_ = lean_nat_div(v___x_2191_, v___x_2192_);
lean_dec(v___x_2191_);
v___x_2194_ = lean_array_get_size(v_buckets_x27_2189_);
v___x_2195_ = lean_nat_dec_le(v___x_2193_, v___x_2194_);
lean_dec(v___x_2193_);
if (v___x_2195_ == 0)
{
lean_object* v_val_2196_; lean_object* v___x_2198_; 
v_val_2196_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_buckets_x27_2189_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 1, v_val_2196_);
lean_ctor_set(v___x_2169_, 0, v_size_x27_2187_);
v___x_2198_ = v___x_2169_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_size_x27_2187_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_val_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
else
{
lean_object* v___x_2201_; 
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 1, v_buckets_x27_2189_);
lean_ctor_set(v___x_2169_, 0, v_size_x27_2187_);
v___x_2201_ = v___x_2169_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_size_x27_2187_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_buckets_x27_2189_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
else
{
lean_object* v___x_2203_; lean_object* v_buckets_x27_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2208_; 
lean_inc(v_bkt_2184_);
v___x_2203_ = lean_box(0);
v_buckets_x27_2204_ = lean_array_uset(v_buckets_2167_, v___x_2183_, v___x_2203_);
v___x_2205_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_2164_, v_b_2165_, v_bkt_2184_);
v___x_2206_ = lean_array_uset(v_buckets_x27_2204_, v___x_2183_, v___x_2205_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 1, v___x_2206_);
v___x_2208_ = v___x_2169_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_size_2166_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object* v_a_2211_, lean_object* v_e_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2215_ = lean_st_ref_take(v_a_2211_);
v___x_2216_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v___x_2215_, v_e_2212_, v_a_2213_);
v___x_2217_ = lean_st_ref_set(v_a_2211_, v___x_2216_);
v___x_2218_ = lean_box(0);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2219_, lean_object* v_e_2220_, lean_object* v_a_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(v_a_2219_, v_e_2220_, v_a_2221_);
lean_dec(v_a_2219_);
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
lean_object* v_binderName_2318_; lean_object* v_binderType_2319_; lean_object* v_body_2320_; uint8_t v_binderInfo_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v_binderName_2318_ = lean_ctor_get(v_e_2310_, 0);
lean_inc(v_binderName_2318_);
v_binderType_2319_ = lean_ctor_get(v_e_2310_, 1);
lean_inc_ref(v_binderType_2319_);
v_body_2320_ = lean_ctor_get(v_e_2310_, 2);
lean_inc_ref(v_body_2320_);
v_binderInfo_2321_ = lean_ctor_get_uint8(v_e_2310_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2310_, 3);
v___x_2322_ = lean_expr_instantiate_rev(v_binderType_2319_, v_fvars_2309_);
lean_dec_ref(v_binderType_2319_);
lean_inc_ref(v_post_2305_);
lean_inc_ref(v_pre_2304_);
v___x_2323_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2304_, v_post_2305_, v_usedLetOnly_2306_, v_skipConstInApp_2307_, v_skipInstances_2308_, v___x_2322_, v_a_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___f_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v___x_2325_ = lean_box(v_usedLetOnly_2306_);
v___x_2326_ = lean_box(v_skipConstInApp_2307_);
v___x_2327_ = lean_box(v_skipInstances_2308_);
v___f_2328_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2328_, 0, v_fvars_2309_);
lean_closure_set(v___f_2328_, 1, v_pre_2304_);
lean_closure_set(v___f_2328_, 2, v_post_2305_);
lean_closure_set(v___f_2328_, 3, v___x_2325_);
lean_closure_set(v___f_2328_, 4, v___x_2326_);
lean_closure_set(v___f_2328_, 5, v___x_2327_);
lean_closure_set(v___f_2328_, 6, v_body_2320_);
v___x_2329_ = 0;
v___x_2330_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2318_, v_binderInfo_2321_, v_a_2324_, v___f_2328_, v___x_2329_, v_a_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
return v___x_2330_;
}
else
{
lean_dec_ref(v_body_2320_);
lean_dec(v_binderName_2318_);
lean_dec_ref(v_fvars_2309_);
lean_dec_ref(v_post_2305_);
lean_dec_ref(v_pre_2304_);
return v___x_2323_;
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
lean_object* v_declName_2390_; lean_object* v_type_2391_; lean_object* v_value_2392_; lean_object* v_body_2393_; uint8_t v_nondep_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
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
v___x_2395_ = lean_expr_instantiate_rev(v_type_2391_, v_fvars_2381_);
lean_dec_ref(v_type_2391_);
lean_inc_ref(v_post_2377_);
lean_inc_ref(v_pre_2376_);
v___x_2396_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2376_, v_post_2377_, v_usedLetOnly_2378_, v_skipConstInApp_2379_, v_skipInstances_2380_, v___x_2395_, v_a_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2396_, 1);
v___x_2398_ = lean_expr_instantiate_rev(v_value_2392_, v_fvars_2381_);
lean_dec_ref(v_value_2392_);
lean_inc_ref(v_post_2377_);
lean_inc_ref(v_pre_2376_);
v___x_2399_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2376_, v_post_2377_, v_usedLetOnly_2378_, v_skipConstInApp_2379_, v_skipInstances_2380_, v___x_2398_, v_a_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___f_2404_; uint8_t v___x_2405_; lean_object* v___x_2406_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref_known(v___x_2399_, 1);
v___x_2401_ = lean_box(v_usedLetOnly_2378_);
v___x_2402_ = lean_box(v_skipConstInApp_2379_);
v___x_2403_ = lean_box(v_skipInstances_2380_);
v___f_2404_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2404_, 0, v_fvars_2381_);
lean_closure_set(v___f_2404_, 1, v_pre_2376_);
lean_closure_set(v___f_2404_, 2, v_post_2377_);
lean_closure_set(v___f_2404_, 3, v___x_2401_);
lean_closure_set(v___f_2404_, 4, v___x_2402_);
lean_closure_set(v___f_2404_, 5, v___x_2403_);
lean_closure_set(v___f_2404_, 6, v_body_2393_);
v___x_2405_ = 0;
v___x_2406_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_2390_, v_a_2397_, v_a_2400_, v___f_2404_, v_nondep_2394_, v___x_2405_, v_a_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
return v___x_2406_;
}
else
{
lean_dec(v_a_2397_);
lean_dec_ref(v_body_2393_);
lean_dec(v_declName_2390_);
lean_dec_ref(v_fvars_2381_);
lean_dec_ref(v_post_2377_);
lean_dec_ref(v_pre_2376_);
return v___x_2399_;
}
}
else
{
lean_dec_ref(v_body_2393_);
lean_dec_ref(v_value_2392_);
lean_dec(v_declName_2390_);
lean_dec_ref(v_fvars_2381_);
lean_dec_ref(v_post_2377_);
lean_dec_ref(v_pre_2376_);
return v___x_2396_;
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
lean_object* v_v_2434_; lean_object* v___x_2435_; 
v_v_2434_ = lean_array_uget_borrowed(v_bs_2424_, v_i_2423_);
lean_inc(v_v_2434_);
lean_inc_ref(v_post_2418_);
lean_inc_ref(v_pre_2417_);
v___x_2435_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2417_, v_post_2418_, v_usedLetOnly_2419_, v_skipConstInApp_2420_, v_skipInstances_2421_, v_v_2434_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2437_; lean_object* v_bs_x27_2438_; size_t v___x_2439_; size_t v___x_2440_; lean_object* v___x_2441_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v___x_2437_ = lean_unsigned_to_nat(0u);
v_bs_x27_2438_ = lean_array_uset(v_bs_2424_, v_i_2423_, v___x_2437_);
v___x_2439_ = ((size_t)1ULL);
v___x_2440_ = lean_usize_add(v_i_2423_, v___x_2439_);
v___x_2441_ = lean_array_uset(v_bs_x27_2438_, v_i_2423_, v_a_2436_);
v_i_2423_ = v___x_2440_;
v_bs_2424_ = v___x_2441_;
goto _start;
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec_ref(v_bs_2424_);
lean_dec_ref(v_post_2418_);
lean_dec_ref(v_pre_2417_);
v_a_2443_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2435_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2435_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_2790_, lean_object* v_pre_2791_, lean_object* v_post_2792_, lean_object* v_usedLetOnly_2793_, lean_object* v_skipConstInApp_2794_, lean_object* v_skipInstances_2795_, lean_object* v_body_2796_, lean_object* v_x_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
uint8_t v_usedLetOnly_boxed_2805_; uint8_t v_skipConstInApp_boxed_2806_; uint8_t v_skipInstances_boxed_2807_; lean_object* v_res_2808_; 
v_usedLetOnly_boxed_2805_ = lean_unbox(v_usedLetOnly_2793_);
v_skipConstInApp_boxed_2806_ = lean_unbox(v_skipConstInApp_2794_);
v_skipInstances_boxed_2807_ = lean_unbox(v_skipInstances_2795_);
v_res_2808_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(v_fvars_2790_, v_pre_2791_, v_post_2792_, v_usedLetOnly_boxed_2805_, v_skipConstInApp_boxed_2806_, v_skipInstances_boxed_2807_, v_body_2796_, v_x_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v___y_2798_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object* v_pre_2809_, lean_object* v_post_2810_, uint8_t v_usedLetOnly_2811_, uint8_t v_skipConstInApp_2812_, uint8_t v_skipInstances_2813_, lean_object* v_fvars_2814_, lean_object* v_e_2815_, lean_object* v_a_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
if (lean_obj_tag(v_e_2815_) == 7)
{
lean_object* v_binderName_2823_; lean_object* v_binderType_2824_; lean_object* v_body_2825_; uint8_t v_binderInfo_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v_binderName_2823_ = lean_ctor_get(v_e_2815_, 0);
lean_inc(v_binderName_2823_);
v_binderType_2824_ = lean_ctor_get(v_e_2815_, 1);
lean_inc_ref(v_binderType_2824_);
v_body_2825_ = lean_ctor_get(v_e_2815_, 2);
lean_inc_ref(v_body_2825_);
v_binderInfo_2826_ = lean_ctor_get_uint8(v_e_2815_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2815_, 3);
v___x_2827_ = lean_expr_instantiate_rev(v_binderType_2824_, v_fvars_2814_);
lean_dec_ref(v_binderType_2824_);
lean_inc_ref(v_post_2810_);
lean_inc_ref(v_pre_2809_);
v___x_2828_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2809_, v_post_2810_, v_usedLetOnly_2811_, v_skipConstInApp_2812_, v_skipInstances_2813_, v___x_2827_, v_a_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___f_2833_; uint8_t v___x_2834_; lean_object* v___x_2835_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v___x_2828_, 1);
v___x_2830_ = lean_box(v_usedLetOnly_2811_);
v___x_2831_ = lean_box(v_skipConstInApp_2812_);
v___x_2832_ = lean_box(v_skipInstances_2813_);
v___f_2833_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2833_, 0, v_fvars_2814_);
lean_closure_set(v___f_2833_, 1, v_pre_2809_);
lean_closure_set(v___f_2833_, 2, v_post_2810_);
lean_closure_set(v___f_2833_, 3, v___x_2830_);
lean_closure_set(v___f_2833_, 4, v___x_2831_);
lean_closure_set(v___f_2833_, 5, v___x_2832_);
lean_closure_set(v___f_2833_, 6, v_body_2825_);
v___x_2834_ = 0;
v___x_2835_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2823_, v_binderInfo_2826_, v_a_2829_, v___f_2833_, v___x_2834_, v_a_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
return v___x_2835_;
}
else
{
lean_dec_ref(v_body_2825_);
lean_dec(v_binderName_2823_);
lean_dec_ref(v_fvars_2814_);
lean_dec_ref(v_post_2810_);
lean_dec_ref(v_pre_2809_);
return v___x_2828_;
}
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = lean_expr_instantiate_rev(v_e_2815_, v_fvars_2814_);
lean_dec_ref(v_e_2815_);
lean_inc_ref(v_post_2810_);
lean_inc_ref(v_pre_2809_);
v___x_2837_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2809_, v_post_2810_, v_usedLetOnly_2811_, v_skipConstInApp_2812_, v_skipInstances_2813_, v___x_2836_, v_a_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; uint8_t v___x_2839_; uint8_t v___x_2840_; uint8_t v___x_2841_; lean_object* v___x_2842_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2838_);
lean_dec_ref_known(v___x_2837_, 1);
v___x_2839_ = 0;
v___x_2840_ = 1;
v___x_2841_ = 1;
v___x_2842_ = l_Lean_Meta_mkForallFVars(v_fvars_2814_, v_a_2838_, v___x_2839_, v_usedLetOnly_2811_, v___x_2840_, v___x_2841_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec_ref(v_fvars_2814_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2844_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2843_);
lean_dec_ref_known(v___x_2842_, 1);
v___x_2844_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2809_, v_post_2810_, v_usedLetOnly_2811_, v_skipConstInApp_2812_, v_skipInstances_2813_, v_a_2843_, v_a_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
return v___x_2844_;
}
else
{
lean_dec_ref(v_post_2810_);
lean_dec_ref(v_pre_2809_);
return v___x_2842_;
}
}
else
{
lean_dec_ref(v_fvars_2814_);
lean_dec_ref(v_post_2810_);
lean_dec_ref(v_pre_2809_);
return v___x_2837_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_2845_, lean_object* v_pre_2846_, lean_object* v_post_2847_, uint8_t v_usedLetOnly_2848_, uint8_t v_skipConstInApp_2849_, uint8_t v_skipInstances_2850_, lean_object* v_body_2851_, lean_object* v_x_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_array_push(v_fvars_2845_, v_x_2852_);
v___x_2861_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2846_, v_post_2847_, v_usedLetOnly_2848_, v_skipConstInApp_2849_, v_skipInstances_2850_, v___x_2860_, v_body_2851_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2862_, lean_object* v_post_2863_, lean_object* v_usedLetOnly_2864_, lean_object* v_skipConstInApp_2865_, lean_object* v_skipInstances_2866_, lean_object* v_e_2867_, lean_object* v_a_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
uint8_t v_usedLetOnly_boxed_2875_; uint8_t v_skipConstInApp_boxed_2876_; uint8_t v_skipInstances_boxed_2877_; lean_object* v_res_2878_; 
v_usedLetOnly_boxed_2875_ = lean_unbox(v_usedLetOnly_2864_);
v_skipConstInApp_boxed_2876_ = lean_unbox(v_skipConstInApp_2865_);
v_skipInstances_boxed_2877_ = lean_unbox(v_skipInstances_2866_);
v_res_2878_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2862_, v_post_2863_, v_usedLetOnly_boxed_2875_, v_skipConstInApp_boxed_2876_, v_skipInstances_boxed_2877_, v_e_2867_, v_a_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec(v_a_2868_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_2879_, lean_object* v_post_2880_, lean_object* v_usedLetOnly_2881_, lean_object* v_skipConstInApp_2882_, lean_object* v_skipInstances_2883_, lean_object* v_sz_2884_, lean_object* v_i_2885_, lean_object* v_bs_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
uint8_t v_usedLetOnly_boxed_2894_; uint8_t v_skipConstInApp_boxed_2895_; uint8_t v_skipInstances_boxed_2896_; size_t v_sz_boxed_2897_; size_t v_i_boxed_2898_; lean_object* v_res_2899_; 
v_usedLetOnly_boxed_2894_ = lean_unbox(v_usedLetOnly_2881_);
v_skipConstInApp_boxed_2895_ = lean_unbox(v_skipConstInApp_2882_);
v_skipInstances_boxed_2896_ = lean_unbox(v_skipInstances_2883_);
v_sz_boxed_2897_ = lean_unbox_usize(v_sz_2884_);
lean_dec(v_sz_2884_);
v_i_boxed_2898_ = lean_unbox_usize(v_i_2885_);
lean_dec(v_i_2885_);
v_res_2899_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2879_, v_post_2880_, v_usedLetOnly_boxed_2894_, v_skipConstInApp_boxed_2895_, v_skipInstances_boxed_2896_, v_sz_boxed_2897_, v_i_boxed_2898_, v_bs_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec(v___y_2887_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object* v_pre_2900_, lean_object* v_post_2901_, lean_object* v_usedLetOnly_2902_, lean_object* v_skipConstInApp_2903_, lean_object* v_skipInstances_2904_, lean_object* v_e_2905_, lean_object* v_a_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
uint8_t v_usedLetOnly_boxed_2913_; uint8_t v_skipConstInApp_boxed_2914_; uint8_t v_skipInstances_boxed_2915_; lean_object* v_res_2916_; 
v_usedLetOnly_boxed_2913_ = lean_unbox(v_usedLetOnly_2902_);
v_skipConstInApp_boxed_2914_ = lean_unbox(v_skipConstInApp_2903_);
v_skipInstances_boxed_2915_ = lean_unbox(v_skipInstances_2904_);
v_res_2916_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2900_, v_post_2901_, v_usedLetOnly_boxed_2913_, v_skipConstInApp_boxed_2914_, v_skipInstances_boxed_2915_, v_e_2905_, v_a_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec(v_a_2906_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_2917_, lean_object* v_post_2918_, lean_object* v_usedLetOnly_2919_, lean_object* v_skipConstInApp_2920_, lean_object* v_skipInstances_2921_, lean_object* v_fvars_2922_, lean_object* v_e_2923_, lean_object* v_a_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
uint8_t v_usedLetOnly_boxed_2931_; uint8_t v_skipConstInApp_boxed_2932_; uint8_t v_skipInstances_boxed_2933_; lean_object* v_res_2934_; 
v_usedLetOnly_boxed_2931_ = lean_unbox(v_usedLetOnly_2919_);
v_skipConstInApp_boxed_2932_ = lean_unbox(v_skipConstInApp_2920_);
v_skipInstances_boxed_2933_ = lean_unbox(v_skipInstances_2921_);
v_res_2934_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2917_, v_post_2918_, v_usedLetOnly_boxed_2931_, v_skipConstInApp_boxed_2932_, v_skipInstances_boxed_2933_, v_fvars_2922_, v_e_2923_, v_a_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec(v_a_2924_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_2935_, lean_object* v_post_2936_, lean_object* v_usedLetOnly_2937_, lean_object* v_skipConstInApp_2938_, lean_object* v_skipInstances_2939_, lean_object* v_fvars_2940_, lean_object* v_e_2941_, lean_object* v_a_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
uint8_t v_usedLetOnly_boxed_2949_; uint8_t v_skipConstInApp_boxed_2950_; uint8_t v_skipInstances_boxed_2951_; lean_object* v_res_2952_; 
v_usedLetOnly_boxed_2949_ = lean_unbox(v_usedLetOnly_2937_);
v_skipConstInApp_boxed_2950_ = lean_unbox(v_skipConstInApp_2938_);
v_skipInstances_boxed_2951_ = lean_unbox(v_skipInstances_2939_);
v_res_2952_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2935_, v_post_2936_, v_usedLetOnly_boxed_2949_, v_skipConstInApp_boxed_2950_, v_skipInstances_boxed_2951_, v_fvars_2940_, v_e_2941_, v_a_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec(v_a_2942_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_2953_, lean_object* v_post_2954_, lean_object* v_usedLetOnly_2955_, lean_object* v_skipConstInApp_2956_, lean_object* v_skipInstances_2957_, lean_object* v_fvars_2958_, lean_object* v_e_2959_, lean_object* v_a_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
uint8_t v_usedLetOnly_boxed_2967_; uint8_t v_skipConstInApp_boxed_2968_; uint8_t v_skipInstances_boxed_2969_; lean_object* v_res_2970_; 
v_usedLetOnly_boxed_2967_ = lean_unbox(v_usedLetOnly_2955_);
v_skipConstInApp_boxed_2968_ = lean_unbox(v_skipConstInApp_2956_);
v_skipInstances_boxed_2969_ = lean_unbox(v_skipInstances_2957_);
v_res_2970_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2953_, v_post_2954_, v_usedLetOnly_boxed_2967_, v_skipConstInApp_boxed_2968_, v_skipInstances_boxed_2969_, v_fvars_2958_, v_e_2959_, v_a_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec(v_a_2960_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_2971_, lean_object* v___x_2972_, lean_object* v_pre_2973_, lean_object* v_post_2974_, lean_object* v_usedLetOnly_2975_, lean_object* v_skipConstInApp_2976_, lean_object* v_skipInstances_2977_, lean_object* v_a_2978_, lean_object* v_b_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
uint8_t v_usedLetOnly_boxed_2987_; uint8_t v_skipConstInApp_boxed_2988_; uint8_t v_skipInstances_boxed_2989_; lean_object* v_res_2990_; 
v_usedLetOnly_boxed_2987_ = lean_unbox(v_usedLetOnly_2975_);
v_skipConstInApp_boxed_2988_ = lean_unbox(v_skipConstInApp_2976_);
v_skipInstances_boxed_2989_ = lean_unbox(v_skipInstances_2977_);
v_res_2990_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_2971_, v___x_2972_, v_pre_2973_, v_post_2974_, v_usedLetOnly_boxed_2987_, v_skipConstInApp_boxed_2988_, v_skipInstances_boxed_2989_, v_a_2978_, v_b_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___x_2972_);
lean_dec(v_upperBound_2971_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_2991_, lean_object* v_pre_2992_, lean_object* v_post_2993_, lean_object* v_usedLetOnly_2994_, lean_object* v_skipConstInApp_2995_, lean_object* v_x_2996_, lean_object* v_x_2997_, lean_object* v_x_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
uint8_t v_skipInstances_boxed_3006_; uint8_t v_usedLetOnly_boxed_3007_; uint8_t v_skipConstInApp_boxed_3008_; lean_object* v_res_3009_; 
v_skipInstances_boxed_3006_ = lean_unbox(v_skipInstances_2991_);
v_usedLetOnly_boxed_3007_ = lean_unbox(v_usedLetOnly_2994_);
v_skipConstInApp_boxed_3008_ = lean_unbox(v_skipConstInApp_2995_);
v_res_3009_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_boxed_3006_, v_pre_2992_, v_post_2993_, v_usedLetOnly_boxed_3007_, v_skipConstInApp_boxed_3008_, v_x_2996_, v_x_2997_, v_x_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec(v___y_2999_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object* v_00_u03b1_3010_, lean_object* v_x_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_apply_1(v_x_3011_, lean_box(0));
v___x_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3020_, lean_object* v_x_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(v_00_u03b1_3020_, v_x_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
return v_res_3028_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3029_ = lean_box(0);
v___x_3030_ = lean_unsigned_to_nat(16u);
v___x_3031_ = lean_mk_array(v___x_3030_, v___x_3029_);
return v___x_3031_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3032_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0);
v___x_3033_ = lean_unsigned_to_nat(0u);
v___x_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
lean_ctor_set(v___x_3034_, 1, v___x_3032_);
return v___x_3034_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3035_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1);
v___x_3036_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3036_, 0, lean_box(0));
lean_closure_set(v___x_3036_, 1, lean_box(0));
lean_closure_set(v___x_3036_, 2, v___x_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object* v_input_3037_, lean_object* v_pre_3038_, lean_object* v_post_3039_, uint8_t v_usedLetOnly_3040_, uint8_t v_skipConstInApp_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v_a_3050_; uint8_t v___x_3051_; lean_object* v___x_3052_; 
v___x_3048_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2);
v___x_3049_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3048_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_a_3050_);
lean_dec_ref(v___x_3049_);
v___x_3051_ = 0;
v___x_3052_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_3038_, v_post_3039_, v_usedLetOnly_3040_, v_skipConstInApp_3041_, v___x_3051_, v_input_3037_, v_a_3050_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 1);
v___x_3054_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3054_, 0, lean_box(0));
lean_closure_set(v___x_3054_, 1, lean_box(0));
lean_closure_set(v___x_3054_, 2, v_a_3050_);
v___x_3055_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3054_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; 
v_unused_3063_ = lean_ctor_get(v___x_3055_, 0);
lean_dec(v_unused_3063_);
v___x_3057_ = v___x_3055_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_dec(v___x_3055_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 0, v_a_3053_);
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3053_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
else
{
lean_dec(v_a_3050_);
return v___x_3052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object* v_input_3064_, lean_object* v_pre_3065_, lean_object* v_post_3066_, lean_object* v_usedLetOnly_3067_, lean_object* v_skipConstInApp_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
uint8_t v_usedLetOnly_boxed_3075_; uint8_t v_skipConstInApp_boxed_3076_; lean_object* v_res_3077_; 
v_usedLetOnly_boxed_3075_ = lean_unbox(v_usedLetOnly_3067_);
v_skipConstInApp_boxed_3076_ = lean_unbox(v_skipConstInApp_3068_);
v_res_3077_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_input_3064_, v_pre_3065_, v_post_3066_, v_usedLetOnly_boxed_3075_, v_skipConstInApp_boxed_3076_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object* v_e_3079_, uint8_t v_elimTrivial_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v_pre_3089_; lean_object* v___f_3090_; uint8_t v___x_3091_; lean_object* v___x_3092_; 
v___x_3086_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_3087_ = lean_st_mk_ref(v___x_3086_);
v___x_3088_ = lean_box(v_elimTrivial_3080_);
v_pre_3089_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed), 8, 1);
lean_closure_set(v_pre_3089_, 0, v___x_3088_);
v___f_3090_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0));
v___x_3091_ = 0;
v___x_3092_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_e_3079_, v_pre_3089_, v___f_3090_, v___x_3091_, v___x_3091_, v___x_3087_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3101_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3095_ = v___x_3092_;
v_isShared_3096_ = v_isSharedCheck_3101_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3092_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3101_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3097_; lean_object* v___x_3099_; 
v___x_3097_ = lean_st_ref_get(v___x_3087_);
lean_dec(v___x_3087_);
lean_dec(v___x_3097_);
if (v_isShared_3096_ == 0)
{
v___x_3099_ = v___x_3095_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3093_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
else
{
lean_dec(v___x_3087_);
return v___x_3092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object* v_e_3102_, lean_object* v_elimTrivial_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_){
_start:
{
uint8_t v_elimTrivial_boxed_3109_; lean_object* v_res_3110_; 
v_elimTrivial_boxed_3109_ = lean_unbox(v_elimTrivial_3103_);
v_res_3110_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v_e_3102_, v_elimTrivial_boxed_3109_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_);
lean_dec(v_a_3107_);
lean_dec_ref(v_a_3106_);
lean_dec(v_a_3105_);
lean_dec_ref(v_a_3104_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object* v_upperBound_3111_, lean_object* v___x_3112_, lean_object* v_pre_3113_, lean_object* v_post_3114_, uint8_t v_usedLetOnly_3115_, uint8_t v_skipConstInApp_3116_, uint8_t v_skipInstances_3117_, lean_object* v___x_3118_, lean_object* v_inst_3119_, lean_object* v_R_3120_, lean_object* v_a_3121_, lean_object* v_b_3122_, lean_object* v_c_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_3111_, v___x_3112_, v_pre_3113_, v_post_3114_, v_usedLetOnly_3115_, v_skipConstInApp_3116_, v_skipInstances_3117_, v_a_3121_, v_b_3122_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_3132_ = _args[0];
lean_object* v___x_3133_ = _args[1];
lean_object* v_pre_3134_ = _args[2];
lean_object* v_post_3135_ = _args[3];
lean_object* v_usedLetOnly_3136_ = _args[4];
lean_object* v_skipConstInApp_3137_ = _args[5];
lean_object* v_skipInstances_3138_ = _args[6];
lean_object* v___x_3139_ = _args[7];
lean_object* v_inst_3140_ = _args[8];
lean_object* v_R_3141_ = _args[9];
lean_object* v_a_3142_ = _args[10];
lean_object* v_b_3143_ = _args[11];
lean_object* v_c_3144_ = _args[12];
lean_object* v___y_3145_ = _args[13];
lean_object* v___y_3146_ = _args[14];
lean_object* v___y_3147_ = _args[15];
lean_object* v___y_3148_ = _args[16];
lean_object* v___y_3149_ = _args[17];
lean_object* v___y_3150_ = _args[18];
lean_object* v___y_3151_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_3152_; uint8_t v_skipConstInApp_boxed_3153_; uint8_t v_skipInstances_boxed_3154_; lean_object* v_res_3155_; 
v_usedLetOnly_boxed_3152_ = lean_unbox(v_usedLetOnly_3136_);
v_skipConstInApp_boxed_3153_ = lean_unbox(v_skipConstInApp_3137_);
v_skipInstances_boxed_3154_ = lean_unbox(v_skipInstances_3138_);
v_res_3155_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_upperBound_3132_, v___x_3133_, v_pre_3134_, v_post_3135_, v_usedLetOnly_boxed_3152_, v_skipConstInApp_boxed_3153_, v_skipInstances_boxed_3154_, v___x_3139_, v_inst_3140_, v_R_3141_, v_a_3142_, v_b_3143_, v_c_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec(v___x_3139_);
lean_dec_ref(v___x_3133_);
lean_dec(v_upperBound_3132_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3156_, lean_object* v_m_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_3157_, v_a_3158_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_3160_, lean_object* v_m_3161_, lean_object* v_a_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(v_00_u03b2_3160_, v_m_3161_, v_a_3162_);
lean_dec_ref(v_a_3162_);
lean_dec_ref(v_m_3161_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_3164_, lean_object* v_name_3165_, uint8_t v_bi_3166_, lean_object* v_type_3167_, lean_object* v_k_3168_, uint8_t v_kind_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_3165_, v_bi_3166_, v_type_3167_, v_k_3168_, v_kind_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3178_, lean_object* v_name_3179_, lean_object* v_bi_3180_, lean_object* v_type_3181_, lean_object* v_k_3182_, lean_object* v_kind_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
uint8_t v_bi_boxed_3191_; uint8_t v_kind_boxed_3192_; lean_object* v_res_3193_; 
v_bi_boxed_3191_ = lean_unbox(v_bi_3180_);
v_kind_boxed_3192_ = lean_unbox(v_kind_3183_);
v_res_3193_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_3178_, v_name_3179_, v_bi_boxed_3191_, v_type_3181_, v_k_3182_, v_kind_boxed_3192_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec(v___y_3184_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_3194_, lean_object* v_name_3195_, lean_object* v_type_3196_, lean_object* v_val_3197_, lean_object* v_k_3198_, uint8_t v_nondep_3199_, uint8_t v_kind_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v___x_3208_; 
v___x_3208_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_3195_, v_type_3196_, v_val_3197_, v_k_3198_, v_nondep_3199_, v_kind_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_3209_, lean_object* v_name_3210_, lean_object* v_type_3211_, lean_object* v_val_3212_, lean_object* v_k_3213_, lean_object* v_nondep_3214_, lean_object* v_kind_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
uint8_t v_nondep_boxed_3223_; uint8_t v_kind_boxed_3224_; lean_object* v_res_3225_; 
v_nondep_boxed_3223_ = lean_unbox(v_nondep_3214_);
v_kind_boxed_3224_ = lean_unbox(v_kind_3215_);
v_res_3225_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_3209_, v_name_3210_, v_type_3211_, v_val_3212_, v_k_3213_, v_nondep_boxed_3223_, v_kind_boxed_3224_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec(v___y_3216_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_3226_, lean_object* v_ref_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
lean_object* v___x_3233_; 
v___x_3233_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_3227_);
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_3234_, lean_object* v_ref_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_3234_, v_ref_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_3242_, lean_object* v_x_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_3252_, lean_object* v_x_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(v_00_u03b1_3252_, v_x_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec(v___y_3254_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_3262_, lean_object* v_m_3263_, lean_object* v_a_3264_, lean_object* v_b_3265_){
_start:
{
lean_object* v___x_3266_; 
v___x_3266_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_m_3263_, v_a_3264_, v_b_3265_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_3267_, lean_object* v_a_3268_, lean_object* v_x_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_a_3268_, v_x_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_3271_, lean_object* v_a_3272_, lean_object* v_x_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_3271_, v_a_3272_, v_x_3273_);
lean_dec(v_x_3273_);
lean_dec_ref(v_a_3272_);
return v_res_3274_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_3275_, lean_object* v_a_3276_, lean_object* v_x_3277_){
_start:
{
uint8_t v___x_3278_; 
v___x_3278_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_a_3276_, v_x_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_3279_, lean_object* v_a_3280_, lean_object* v_x_3281_){
_start:
{
uint8_t v_res_3282_; lean_object* v_r_3283_; 
v_res_3282_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_3279_, v_a_3280_, v_x_3281_);
lean_dec(v_x_3281_);
lean_dec_ref(v_a_3280_);
v_r_3283_ = lean_box(v_res_3282_);
return v_r_3283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16(lean_object* v_00_u03b2_3284_, lean_object* v_data_3285_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16___redArg(v_data_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17(lean_object* v_00_u03b2_3287_, lean_object* v_a_3288_, lean_object* v_b_3289_, lean_object* v_x_3290_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__17___redArg(v_a_3288_, v_b_3289_, v_x_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17(lean_object* v_00_u03b2_3292_, lean_object* v_i_3293_, lean_object* v_source_3294_, lean_object* v_target_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17___redArg(v_i_3293_, v_source_3294_, v_target_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18(lean_object* v_00_u03b2_3297_, lean_object* v_x_3298_, lean_object* v_x_3299_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__16_spec__17_spec__18___redArg(v_x_3298_, v_x_3299_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(lean_object* v_mvarId_3301_, lean_object* v_x_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3301_, v_x_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
v_a_3317_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3308_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3308_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(lean_object* v_mvarId_3325_, lean_object* v_x_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3325_, v_x_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_object* v_00_u03b1_3333_, lean_object* v_mvarId_3334_, lean_object* v_x_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3334_, v_x_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(lean_object* v_00_u03b1_3342_, lean_object* v_mvarId_3343_, lean_object* v_x_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(v_00_u03b1_3342_, v_mvarId_3343_, v_x_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(uint8_t v_elimTrivial_3351_, lean_object* v_as_3352_, size_t v_sz_3353_, size_t v_i_3354_, lean_object* v_b_3355_){
_start:
{
uint8_t v___x_3357_; 
v___x_3357_ = lean_usize_dec_lt(v_i_3354_, v_sz_3353_);
if (v___x_3357_ == 0)
{
lean_object* v___x_3358_; 
v___x_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3358_, 0, v_b_3355_);
return v___x_3358_;
}
else
{
lean_object* v_snd_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3406_; 
v_snd_3359_ = lean_ctor_get(v_b_3355_, 1);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_b_3355_);
if (v_isSharedCheck_3406_ == 0)
{
lean_object* v_unused_3407_; 
v_unused_3407_ = lean_ctor_get(v_b_3355_, 0);
lean_dec(v_unused_3407_);
v___x_3361_ = v_b_3355_;
v_isShared_3362_ = v_isSharedCheck_3406_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_snd_3359_);
lean_dec(v_b_3355_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3406_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3363_; lean_object* v_a_3365_; lean_object* v_a_3372_; 
v___x_3363_ = lean_box(0);
v_a_3372_ = lean_array_uget_borrowed(v_as_3352_, v_i_3354_);
if (lean_obj_tag(v_a_3372_) == 0)
{
v_a_3365_ = v_snd_3359_;
goto v___jp_3364_;
}
else
{
lean_object* v_val_3373_; lean_object* v_fst_3374_; lean_object* v_snd_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3405_; 
v_val_3373_ = lean_ctor_get(v_a_3372_, 0);
v_fst_3374_ = lean_ctor_get(v_snd_3359_, 0);
v_snd_3375_ = lean_ctor_get(v_snd_3359_, 1);
v_isSharedCheck_3405_ = !lean_is_exclusive(v_snd_3359_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3377_ = v_snd_3359_;
v_isShared_3378_ = v_isSharedCheck_3405_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_snd_3375_);
lean_inc(v_fst_3374_);
lean_dec(v_snd_3359_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3405_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
uint8_t v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = 0;
v___x_3380_ = l_Lean_LocalDecl_value_x3f(v_val_3373_, v___x_3379_);
if (lean_obj_tag(v___x_3380_) == 1)
{
lean_object* v_val_3381_; lean_object* v___x_3382_; 
v_val_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_val_3381_);
lean_dec_ref_known(v___x_3380_, 1);
v___x_3382_ = l_Lean_LocalDecl_type(v_val_3373_);
if (lean_obj_tag(v___x_3382_) == 10)
{
lean_object* v_data_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; uint8_t v___x_3387_; uint8_t v___x_3388_; 
v_data_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_data_3383_);
lean_dec_ref_known(v___x_3382_, 2);
v___x_3384_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3385_ = lean_unsigned_to_nat(2u);
v___x_3386_ = l_Lean_KVMap_getNat(v_data_3383_, v___x_3384_, v___x_3385_);
lean_dec(v_data_3383_);
v___x_3387_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3386_);
lean_dec(v___x_3386_);
v___x_3388_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3387_, v_val_3381_, v_elimTrivial_3351_);
if (v___x_3388_ == 0)
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3389_ = l_Lean_LocalDecl_fvarId(v_val_3373_);
v___x_3390_ = l_Lean_mkFVar(v___x_3389_);
v___x_3391_ = lean_array_push(v_fst_3374_, v___x_3390_);
v___x_3392_ = lean_array_push(v_snd_3375_, v_val_3381_);
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 1, v___x_3392_);
lean_ctor_set(v___x_3377_, 0, v___x_3391_);
v___x_3394_ = v___x_3377_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3391_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
v_a_3365_ = v___x_3394_;
goto v___jp_3364_;
}
}
else
{
lean_object* v___x_3397_; 
lean_dec(v_val_3381_);
if (v_isShared_3378_ == 0)
{
v___x_3397_ = v___x_3377_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_fst_3374_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v_snd_3375_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
v_a_3365_ = v___x_3397_;
goto v___jp_3364_;
}
}
}
else
{
lean_object* v___x_3400_; 
lean_dec_ref(v___x_3382_);
lean_dec(v_val_3381_);
if (v_isShared_3378_ == 0)
{
v___x_3400_ = v___x_3377_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_fst_3374_);
lean_ctor_set(v_reuseFailAlloc_3401_, 1, v_snd_3375_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
v_a_3365_ = v___x_3400_;
goto v___jp_3364_;
}
}
}
else
{
lean_object* v___x_3403_; 
lean_dec(v___x_3380_);
if (v_isShared_3378_ == 0)
{
v___x_3403_ = v___x_3377_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_fst_3374_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_snd_3375_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
v_a_3365_ = v___x_3403_;
goto v___jp_3364_;
}
}
}
}
v___jp_3364_:
{
lean_object* v___x_3367_; 
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 1, v_a_3365_);
lean_ctor_set(v___x_3361_, 0, v___x_3363_);
v___x_3367_ = v___x_3361_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v_a_3365_);
v___x_3367_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
size_t v___x_3368_; size_t v___x_3369_; 
v___x_3368_ = ((size_t)1ULL);
v___x_3369_ = lean_usize_add(v_i_3354_, v___x_3368_);
v_i_3354_ = v___x_3369_;
v_b_3355_ = v___x_3367_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_elimTrivial_3408_, lean_object* v_as_3409_, lean_object* v_sz_3410_, lean_object* v_i_3411_, lean_object* v_b_3412_, lean_object* v___y_3413_){
_start:
{
uint8_t v_elimTrivial_boxed_3414_; size_t v_sz_boxed_3415_; size_t v_i_boxed_3416_; lean_object* v_res_3417_; 
v_elimTrivial_boxed_3414_ = lean_unbox(v_elimTrivial_3408_);
v_sz_boxed_3415_ = lean_unbox_usize(v_sz_3410_);
lean_dec(v_sz_3410_);
v_i_boxed_3416_ = lean_unbox_usize(v_i_3411_);
lean_dec(v_i_3411_);
v_res_3417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_boxed_3414_, v_as_3409_, v_sz_boxed_3415_, v_i_boxed_3416_, v_b_3412_);
lean_dec_ref(v_as_3409_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(uint8_t v_elimTrivial_3418_, lean_object* v_as_3419_, size_t v_sz_3420_, size_t v_i_3421_, lean_object* v_b_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
uint8_t v___x_3428_; 
v___x_3428_ = lean_usize_dec_lt(v_i_3421_, v_sz_3420_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3429_; 
v___x_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3429_, 0, v_b_3422_);
return v___x_3429_;
}
else
{
lean_object* v_snd_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3477_; 
v_snd_3430_ = lean_ctor_get(v_b_3422_, 1);
v_isSharedCheck_3477_ = !lean_is_exclusive(v_b_3422_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v_b_3422_, 0);
lean_dec(v_unused_3478_);
v___x_3432_ = v_b_3422_;
v_isShared_3433_ = v_isSharedCheck_3477_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_snd_3430_);
lean_dec(v_b_3422_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3477_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; lean_object* v_a_3436_; lean_object* v_a_3443_; 
v___x_3434_ = lean_box(0);
v_a_3443_ = lean_array_uget_borrowed(v_as_3419_, v_i_3421_);
if (lean_obj_tag(v_a_3443_) == 0)
{
v_a_3436_ = v_snd_3430_;
goto v___jp_3435_;
}
else
{
lean_object* v_val_3444_; lean_object* v_fst_3445_; lean_object* v_snd_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3476_; 
v_val_3444_ = lean_ctor_get(v_a_3443_, 0);
v_fst_3445_ = lean_ctor_get(v_snd_3430_, 0);
v_snd_3446_ = lean_ctor_get(v_snd_3430_, 1);
v_isSharedCheck_3476_ = !lean_is_exclusive(v_snd_3430_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3448_ = v_snd_3430_;
v_isShared_3449_ = v_isSharedCheck_3476_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_snd_3446_);
lean_inc(v_fst_3445_);
lean_dec(v_snd_3430_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3476_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
uint8_t v___x_3450_; lean_object* v___x_3451_; 
v___x_3450_ = 0;
v___x_3451_ = l_Lean_LocalDecl_value_x3f(v_val_3444_, v___x_3450_);
if (lean_obj_tag(v___x_3451_) == 1)
{
lean_object* v_val_3452_; lean_object* v___x_3453_; 
v_val_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_val_3452_);
lean_dec_ref_known(v___x_3451_, 1);
v___x_3453_ = l_Lean_LocalDecl_type(v_val_3444_);
if (lean_obj_tag(v___x_3453_) == 10)
{
lean_object* v_data_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; uint8_t v___x_3458_; uint8_t v___x_3459_; 
v_data_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_data_3454_);
lean_dec_ref_known(v___x_3453_, 2);
v___x_3455_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3456_ = lean_unsigned_to_nat(2u);
v___x_3457_ = l_Lean_KVMap_getNat(v_data_3454_, v___x_3455_, v___x_3456_);
lean_dec(v_data_3454_);
v___x_3458_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3457_);
lean_dec(v___x_3457_);
v___x_3459_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3458_, v_val_3452_, v_elimTrivial_3418_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3460_ = l_Lean_LocalDecl_fvarId(v_val_3444_);
v___x_3461_ = l_Lean_mkFVar(v___x_3460_);
v___x_3462_ = lean_array_push(v_fst_3445_, v___x_3461_);
v___x_3463_ = lean_array_push(v_snd_3446_, v_val_3452_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 1, v___x_3463_);
lean_ctor_set(v___x_3448_, 0, v___x_3462_);
v___x_3465_ = v___x_3448_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3462_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
v_a_3436_ = v___x_3465_;
goto v___jp_3435_;
}
}
else
{
lean_object* v___x_3468_; 
lean_dec(v_val_3452_);
if (v_isShared_3449_ == 0)
{
v___x_3468_ = v___x_3448_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_fst_3445_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_snd_3446_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
v_a_3436_ = v___x_3468_;
goto v___jp_3435_;
}
}
}
else
{
lean_object* v___x_3471_; 
lean_dec_ref(v___x_3453_);
lean_dec(v_val_3452_);
if (v_isShared_3449_ == 0)
{
v___x_3471_ = v___x_3448_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_fst_3445_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_snd_3446_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
v_a_3436_ = v___x_3471_;
goto v___jp_3435_;
}
}
}
else
{
lean_object* v___x_3474_; 
lean_dec(v___x_3451_);
if (v_isShared_3449_ == 0)
{
v___x_3474_ = v___x_3448_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_fst_3445_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v_snd_3446_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
v_a_3436_ = v___x_3474_;
goto v___jp_3435_;
}
}
}
}
v___jp_3435_:
{
lean_object* v___x_3438_; 
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 1, v_a_3436_);
lean_ctor_set(v___x_3432_, 0, v___x_3434_);
v___x_3438_ = v___x_3432_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3434_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v_a_3436_);
v___x_3438_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
size_t v___x_3439_; size_t v___x_3440_; lean_object* v___x_3441_; 
v___x_3439_ = ((size_t)1ULL);
v___x_3440_ = lean_usize_add(v_i_3421_, v___x_3439_);
v___x_3441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_3418_, v_as_3419_, v_sz_3420_, v___x_3440_, v___x_3438_);
return v___x_3441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(lean_object* v_elimTrivial_3479_, lean_object* v_as_3480_, lean_object* v_sz_3481_, lean_object* v_i_3482_, lean_object* v_b_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
uint8_t v_elimTrivial_boxed_3489_; size_t v_sz_boxed_3490_; size_t v_i_boxed_3491_; lean_object* v_res_3492_; 
v_elimTrivial_boxed_3489_ = lean_unbox(v_elimTrivial_3479_);
v_sz_boxed_3490_ = lean_unbox_usize(v_sz_3481_);
lean_dec(v_sz_3481_);
v_i_boxed_3491_ = lean_unbox_usize(v_i_3482_);
lean_dec(v_i_3482_);
v_res_3492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_boxed_3489_, v_as_3480_, v_sz_boxed_3490_, v_i_boxed_3491_, v_b_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec_ref(v_as_3480_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(uint8_t v_elimTrivial_3493_, lean_object* v_as_3494_, size_t v_sz_3495_, size_t v_i_3496_, lean_object* v_b_3497_){
_start:
{
uint8_t v___x_3499_; 
v___x_3499_ = lean_usize_dec_lt(v_i_3496_, v_sz_3495_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3500_; 
v___x_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3500_, 0, v_b_3497_);
return v___x_3500_;
}
else
{
lean_object* v_snd_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3548_; 
v_snd_3501_ = lean_ctor_get(v_b_3497_, 1);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_b_3497_);
if (v_isSharedCheck_3548_ == 0)
{
lean_object* v_unused_3549_; 
v_unused_3549_ = lean_ctor_get(v_b_3497_, 0);
lean_dec(v_unused_3549_);
v___x_3503_ = v_b_3497_;
v_isShared_3504_ = v_isSharedCheck_3548_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_snd_3501_);
lean_dec(v_b_3497_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3548_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3505_; lean_object* v_a_3507_; lean_object* v_a_3514_; 
v___x_3505_ = lean_box(0);
v_a_3514_ = lean_array_uget_borrowed(v_as_3494_, v_i_3496_);
if (lean_obj_tag(v_a_3514_) == 0)
{
v_a_3507_ = v_snd_3501_;
goto v___jp_3506_;
}
else
{
lean_object* v_val_3515_; lean_object* v_fst_3516_; lean_object* v_snd_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3547_; 
v_val_3515_ = lean_ctor_get(v_a_3514_, 0);
v_fst_3516_ = lean_ctor_get(v_snd_3501_, 0);
v_snd_3517_ = lean_ctor_get(v_snd_3501_, 1);
v_isSharedCheck_3547_ = !lean_is_exclusive(v_snd_3501_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3519_ = v_snd_3501_;
v_isShared_3520_ = v_isSharedCheck_3547_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_snd_3517_);
lean_inc(v_fst_3516_);
lean_dec(v_snd_3501_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3547_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
uint8_t v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = 0;
v___x_3522_ = l_Lean_LocalDecl_value_x3f(v_val_3515_, v___x_3521_);
if (lean_obj_tag(v___x_3522_) == 1)
{
lean_object* v_val_3523_; lean_object* v___x_3524_; 
v_val_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_val_3523_);
lean_dec_ref_known(v___x_3522_, 1);
v___x_3524_ = l_Lean_LocalDecl_type(v_val_3515_);
if (lean_obj_tag(v___x_3524_) == 10)
{
lean_object* v_data_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; uint8_t v___x_3529_; uint8_t v___x_3530_; 
v_data_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_data_3525_);
lean_dec_ref_known(v___x_3524_, 2);
v___x_3526_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3527_ = lean_unsigned_to_nat(2u);
v___x_3528_ = l_Lean_KVMap_getNat(v_data_3525_, v___x_3526_, v___x_3527_);
lean_dec(v_data_3525_);
v___x_3529_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3528_);
lean_dec(v___x_3528_);
v___x_3530_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3529_, v_val_3523_, v_elimTrivial_3493_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3536_; 
v___x_3531_ = l_Lean_LocalDecl_fvarId(v_val_3515_);
v___x_3532_ = l_Lean_mkFVar(v___x_3531_);
v___x_3533_ = lean_array_push(v_fst_3516_, v___x_3532_);
v___x_3534_ = lean_array_push(v_snd_3517_, v_val_3523_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v___x_3534_);
lean_ctor_set(v___x_3519_, 0, v___x_3533_);
v___x_3536_ = v___x_3519_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3533_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
v_a_3507_ = v___x_3536_;
goto v___jp_3506_;
}
}
else
{
lean_object* v___x_3539_; 
lean_dec(v_val_3523_);
if (v_isShared_3520_ == 0)
{
v___x_3539_ = v___x_3519_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_fst_3516_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v_snd_3517_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
v_a_3507_ = v___x_3539_;
goto v___jp_3506_;
}
}
}
else
{
lean_object* v___x_3542_; 
lean_dec_ref(v___x_3524_);
lean_dec(v_val_3523_);
if (v_isShared_3520_ == 0)
{
v___x_3542_ = v___x_3519_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_fst_3516_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v_snd_3517_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
v_a_3507_ = v___x_3542_;
goto v___jp_3506_;
}
}
}
else
{
lean_object* v___x_3545_; 
lean_dec(v___x_3522_);
if (v_isShared_3520_ == 0)
{
v___x_3545_ = v___x_3519_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_fst_3516_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v_snd_3517_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
v_a_3507_ = v___x_3545_;
goto v___jp_3506_;
}
}
}
}
v___jp_3506_:
{
lean_object* v___x_3509_; 
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 1, v_a_3507_);
lean_ctor_set(v___x_3503_, 0, v___x_3505_);
v___x_3509_ = v___x_3503_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3505_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v_a_3507_);
v___x_3509_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
size_t v___x_3510_; size_t v___x_3511_; 
v___x_3510_ = ((size_t)1ULL);
v___x_3511_ = lean_usize_add(v_i_3496_, v___x_3510_);
v_i_3496_ = v___x_3511_;
v_b_3497_ = v___x_3509_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_elimTrivial_3550_, lean_object* v_as_3551_, lean_object* v_sz_3552_, lean_object* v_i_3553_, lean_object* v_b_3554_, lean_object* v___y_3555_){
_start:
{
uint8_t v_elimTrivial_boxed_3556_; size_t v_sz_boxed_3557_; size_t v_i_boxed_3558_; lean_object* v_res_3559_; 
v_elimTrivial_boxed_3556_ = lean_unbox(v_elimTrivial_3550_);
v_sz_boxed_3557_ = lean_unbox_usize(v_sz_3552_);
lean_dec(v_sz_3552_);
v_i_boxed_3558_ = lean_unbox_usize(v_i_3553_);
lean_dec(v_i_3553_);
v_res_3559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_boxed_3556_, v_as_3551_, v_sz_boxed_3557_, v_i_boxed_3558_, v_b_3554_);
lean_dec_ref(v_as_3551_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(uint8_t v_elimTrivial_3560_, lean_object* v_as_3561_, size_t v_sz_3562_, size_t v_i_3563_, lean_object* v_b_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
uint8_t v___x_3570_; 
v___x_3570_ = lean_usize_dec_lt(v_i_3563_, v_sz_3562_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; 
v___x_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3571_, 0, v_b_3564_);
return v___x_3571_;
}
else
{
lean_object* v_snd_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3619_; 
v_snd_3572_ = lean_ctor_get(v_b_3564_, 1);
v_isSharedCheck_3619_ = !lean_is_exclusive(v_b_3564_);
if (v_isSharedCheck_3619_ == 0)
{
lean_object* v_unused_3620_; 
v_unused_3620_ = lean_ctor_get(v_b_3564_, 0);
lean_dec(v_unused_3620_);
v___x_3574_ = v_b_3564_;
v_isShared_3575_ = v_isSharedCheck_3619_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_snd_3572_);
lean_dec(v_b_3564_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3619_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; lean_object* v_a_3578_; lean_object* v_a_3585_; 
v___x_3576_ = lean_box(0);
v_a_3585_ = lean_array_uget_borrowed(v_as_3561_, v_i_3563_);
if (lean_obj_tag(v_a_3585_) == 0)
{
v_a_3578_ = v_snd_3572_;
goto v___jp_3577_;
}
else
{
lean_object* v_val_3586_; lean_object* v_fst_3587_; lean_object* v_snd_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3618_; 
v_val_3586_ = lean_ctor_get(v_a_3585_, 0);
v_fst_3587_ = lean_ctor_get(v_snd_3572_, 0);
v_snd_3588_ = lean_ctor_get(v_snd_3572_, 1);
v_isSharedCheck_3618_ = !lean_is_exclusive(v_snd_3572_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3590_ = v_snd_3572_;
v_isShared_3591_ = v_isSharedCheck_3618_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_snd_3588_);
lean_inc(v_fst_3587_);
lean_dec(v_snd_3572_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3618_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
uint8_t v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = 0;
v___x_3593_ = l_Lean_LocalDecl_value_x3f(v_val_3586_, v___x_3592_);
if (lean_obj_tag(v___x_3593_) == 1)
{
lean_object* v_val_3594_; lean_object* v___x_3595_; 
v_val_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_val_3594_);
lean_dec_ref_known(v___x_3593_, 1);
v___x_3595_ = l_Lean_LocalDecl_type(v_val_3586_);
if (lean_obj_tag(v___x_3595_) == 10)
{
lean_object* v_data_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; uint8_t v___x_3600_; uint8_t v___x_3601_; 
v_data_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_data_3596_);
lean_dec_ref_known(v___x_3595_, 2);
v___x_3597_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3598_ = lean_unsigned_to_nat(2u);
v___x_3599_ = l_Lean_KVMap_getNat(v_data_3596_, v___x_3597_, v___x_3598_);
lean_dec(v_data_3596_);
v___x_3600_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3599_);
lean_dec(v___x_3599_);
v___x_3601_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3600_, v_val_3594_, v_elimTrivial_3560_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3607_; 
v___x_3602_ = l_Lean_LocalDecl_fvarId(v_val_3586_);
v___x_3603_ = l_Lean_mkFVar(v___x_3602_);
v___x_3604_ = lean_array_push(v_fst_3587_, v___x_3603_);
v___x_3605_ = lean_array_push(v_snd_3588_, v_val_3594_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 1, v___x_3605_);
lean_ctor_set(v___x_3590_, 0, v___x_3604_);
v___x_3607_ = v___x_3590_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3604_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
v_a_3578_ = v___x_3607_;
goto v___jp_3577_;
}
}
else
{
lean_object* v___x_3610_; 
lean_dec(v_val_3594_);
if (v_isShared_3591_ == 0)
{
v___x_3610_ = v___x_3590_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_fst_3587_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_snd_3588_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
v_a_3578_ = v___x_3610_;
goto v___jp_3577_;
}
}
}
else
{
lean_object* v___x_3613_; 
lean_dec_ref(v___x_3595_);
lean_dec(v_val_3594_);
if (v_isShared_3591_ == 0)
{
v___x_3613_ = v___x_3590_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_fst_3587_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v_snd_3588_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
v_a_3578_ = v___x_3613_;
goto v___jp_3577_;
}
}
}
else
{
lean_object* v___x_3616_; 
lean_dec(v___x_3593_);
if (v_isShared_3591_ == 0)
{
v___x_3616_ = v___x_3590_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_fst_3587_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_snd_3588_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
v_a_3578_ = v___x_3616_;
goto v___jp_3577_;
}
}
}
}
v___jp_3577_:
{
lean_object* v___x_3580_; 
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 1, v_a_3578_);
lean_ctor_set(v___x_3574_, 0, v___x_3576_);
v___x_3580_ = v___x_3574_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3576_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v_a_3578_);
v___x_3580_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
size_t v___x_3581_; size_t v___x_3582_; lean_object* v___x_3583_; 
v___x_3581_ = ((size_t)1ULL);
v___x_3582_ = lean_usize_add(v_i_3563_, v___x_3581_);
v___x_3583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_3560_, v_as_3561_, v_sz_3562_, v___x_3582_, v___x_3580_);
return v___x_3583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(lean_object* v_elimTrivial_3621_, lean_object* v_as_3622_, lean_object* v_sz_3623_, lean_object* v_i_3624_, lean_object* v_b_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
uint8_t v_elimTrivial_boxed_3631_; size_t v_sz_boxed_3632_; size_t v_i_boxed_3633_; lean_object* v_res_3634_; 
v_elimTrivial_boxed_3631_ = lean_unbox(v_elimTrivial_3621_);
v_sz_boxed_3632_ = lean_unbox_usize(v_sz_3623_);
lean_dec(v_sz_3623_);
v_i_boxed_3633_ = lean_unbox_usize(v_i_3624_);
lean_dec(v_i_3624_);
v_res_3634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_boxed_3631_, v_as_3622_, v_sz_boxed_3632_, v_i_boxed_3633_, v_b_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec_ref(v_as_3622_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(lean_object* v_init_3635_, uint8_t v_elimTrivial_3636_, lean_object* v_n_3637_, lean_object* v_b_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
if (lean_obj_tag(v_n_3637_) == 0)
{
lean_object* v_cs_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; size_t v_sz_3647_; size_t v___x_3648_; lean_object* v___x_3649_; 
v_cs_3644_ = lean_ctor_get(v_n_3637_, 0);
v___x_3645_ = lean_box(0);
v___x_3646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
lean_ctor_set(v___x_3646_, 1, v_b_3638_);
v_sz_3647_ = lean_array_size(v_cs_3644_);
v___x_3648_ = ((size_t)0ULL);
v___x_3649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3635_, v_elimTrivial_3636_, v_cs_3644_, v_sz_3647_, v___x_3648_, v___x_3646_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3664_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3652_ = v___x_3649_;
v_isShared_3653_ = v_isSharedCheck_3664_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3664_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v_fst_3654_; 
v_fst_3654_ = lean_ctor_get(v_a_3650_, 0);
if (lean_obj_tag(v_fst_3654_) == 0)
{
lean_object* v_snd_3655_; lean_object* v___x_3656_; lean_object* v___x_3658_; 
v_snd_3655_ = lean_ctor_get(v_a_3650_, 1);
lean_inc(v_snd_3655_);
lean_dec(v_a_3650_);
v___x_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3656_, 0, v_snd_3655_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v___x_3656_);
v___x_3658_ = v___x_3652_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3656_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
else
{
lean_object* v_val_3660_; lean_object* v___x_3662_; 
lean_inc_ref(v_fst_3654_);
lean_dec(v_a_3650_);
v_val_3660_ = lean_ctor_get(v_fst_3654_, 0);
lean_inc(v_val_3660_);
lean_dec_ref_known(v_fst_3654_, 1);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v_val_3660_);
v___x_3662_ = v___x_3652_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_val_3660_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
else
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
v_a_3665_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3649_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3649_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
else
{
lean_object* v_vs_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; size_t v_sz_3676_; size_t v___x_3677_; lean_object* v___x_3678_; 
v_vs_3673_ = lean_ctor_get(v_n_3637_, 0);
v___x_3674_ = lean_box(0);
v___x_3675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3674_);
lean_ctor_set(v___x_3675_, 1, v_b_3638_);
v_sz_3676_ = lean_array_size(v_vs_3673_);
v___x_3677_ = ((size_t)0ULL);
v___x_3678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_3636_, v_vs_3673_, v_sz_3676_, v___x_3677_, v___x_3675_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3693_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3681_ = v___x_3678_;
v_isShared_3682_ = v_isSharedCheck_3693_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3678_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3693_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v_fst_3683_; 
v_fst_3683_ = lean_ctor_get(v_a_3679_, 0);
if (lean_obj_tag(v_fst_3683_) == 0)
{
lean_object* v_snd_3684_; lean_object* v___x_3685_; lean_object* v___x_3687_; 
v_snd_3684_ = lean_ctor_get(v_a_3679_, 1);
lean_inc(v_snd_3684_);
lean_dec(v_a_3679_);
v___x_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3685_, 0, v_snd_3684_);
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 0, v___x_3685_);
v___x_3687_ = v___x_3681_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3685_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
else
{
lean_object* v_val_3689_; lean_object* v___x_3691_; 
lean_inc_ref(v_fst_3683_);
lean_dec(v_a_3679_);
v_val_3689_ = lean_ctor_get(v_fst_3683_, 0);
lean_inc(v_val_3689_);
lean_dec_ref_known(v_fst_3683_, 1);
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 0, v_val_3689_);
v___x_3691_ = v___x_3681_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_val_3689_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
v_a_3694_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3678_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3678_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(lean_object* v_init_3702_, uint8_t v_elimTrivial_3703_, lean_object* v_as_3704_, size_t v_sz_3705_, size_t v_i_3706_, lean_object* v_b_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
uint8_t v___x_3713_; 
v___x_3713_ = lean_usize_dec_lt(v_i_3706_, v_sz_3705_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; 
v___x_3714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3714_, 0, v_b_3707_);
return v___x_3714_;
}
else
{
lean_object* v_snd_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3749_; 
v_snd_3715_ = lean_ctor_get(v_b_3707_, 1);
v_isSharedCheck_3749_ = !lean_is_exclusive(v_b_3707_);
if (v_isSharedCheck_3749_ == 0)
{
lean_object* v_unused_3750_; 
v_unused_3750_ = lean_ctor_get(v_b_3707_, 0);
lean_dec(v_unused_3750_);
v___x_3717_ = v_b_3707_;
v_isShared_3718_ = v_isSharedCheck_3749_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_snd_3715_);
lean_dec(v_b_3707_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3749_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v_a_3719_; lean_object* v___x_3720_; 
v_a_3719_ = lean_array_uget_borrowed(v_as_3704_, v_i_3706_);
lean_inc(v_snd_3715_);
v___x_3720_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3702_, v_elimTrivial_3703_, v_a_3719_, v_snd_3715_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3740_; 
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3723_ = v___x_3720_;
v_isShared_3724_ = v_isSharedCheck_3740_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3720_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3740_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
if (lean_obj_tag(v_a_3721_) == 0)
{
lean_object* v___x_3725_; lean_object* v___x_3727_; 
v___x_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3725_, 0, v_a_3721_);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 0, v___x_3725_);
v___x_3727_ = v___x_3717_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3725_);
lean_ctor_set(v_reuseFailAlloc_3731_, 1, v_snd_3715_);
v___x_3727_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3729_; 
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v___x_3727_);
v___x_3729_ = v___x_3723_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3727_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
else
{
lean_object* v_a_3732_; lean_object* v___x_3733_; lean_object* v___x_3735_; 
lean_del_object(v___x_3723_);
lean_dec(v_snd_3715_);
v_a_3732_ = lean_ctor_get(v_a_3721_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v_a_3721_, 1);
v___x_3733_ = lean_box(0);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 1, v_a_3732_);
lean_ctor_set(v___x_3717_, 0, v___x_3733_);
v___x_3735_ = v___x_3717_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3733_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v_a_3732_);
v___x_3735_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
size_t v___x_3736_; size_t v___x_3737_; 
v___x_3736_ = ((size_t)1ULL);
v___x_3737_ = lean_usize_add(v_i_3706_, v___x_3736_);
v_i_3706_ = v___x_3737_;
v_b_3707_ = v___x_3735_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_del_object(v___x_3717_);
lean_dec(v_snd_3715_);
v_a_3741_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3720_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3720_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(lean_object* v_init_3751_, lean_object* v_elimTrivial_3752_, lean_object* v_as_3753_, lean_object* v_sz_3754_, lean_object* v_i_3755_, lean_object* v_b_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
uint8_t v_elimTrivial_boxed_3762_; size_t v_sz_boxed_3763_; size_t v_i_boxed_3764_; lean_object* v_res_3765_; 
v_elimTrivial_boxed_3762_ = lean_unbox(v_elimTrivial_3752_);
v_sz_boxed_3763_ = lean_unbox_usize(v_sz_3754_);
lean_dec(v_sz_3754_);
v_i_boxed_3764_ = lean_unbox_usize(v_i_3755_);
lean_dec(v_i_3755_);
v_res_3765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3751_, v_elimTrivial_boxed_3762_, v_as_3753_, v_sz_boxed_3763_, v_i_boxed_3764_, v_b_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v_as_3753_);
lean_dec_ref(v_init_3751_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(lean_object* v_init_3766_, lean_object* v_elimTrivial_3767_, lean_object* v_n_3768_, lean_object* v_b_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
uint8_t v_elimTrivial_boxed_3775_; lean_object* v_res_3776_; 
v_elimTrivial_boxed_3775_ = lean_unbox(v_elimTrivial_3767_);
v_res_3776_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3766_, v_elimTrivial_boxed_3775_, v_n_3768_, v_b_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec_ref(v_n_3768_);
lean_dec_ref(v_init_3766_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(uint8_t v_elimTrivial_3777_, lean_object* v_t_3778_, lean_object* v_init_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v_root_3785_; lean_object* v_tail_3786_; lean_object* v___x_3787_; 
v_root_3785_ = lean_ctor_get(v_t_3778_, 0);
v_tail_3786_ = lean_ctor_get(v_t_3778_, 1);
lean_inc_ref(v_init_3779_);
v___x_3787_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3779_, v_elimTrivial_3777_, v_root_3785_, v_init_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
lean_dec_ref(v_init_3779_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3824_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3790_ = v___x_3787_;
v_isShared_3791_ = v_isSharedCheck_3824_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3787_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3824_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
if (lean_obj_tag(v_a_3788_) == 0)
{
lean_object* v_a_3792_; lean_object* v___x_3794_; 
v_a_3792_ = lean_ctor_get(v_a_3788_, 0);
lean_inc(v_a_3792_);
lean_dec_ref_known(v_a_3788_, 1);
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 0, v_a_3792_);
v___x_3794_ = v___x_3790_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3792_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
else
{
lean_object* v_a_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; size_t v_sz_3799_; size_t v___x_3800_; lean_object* v___x_3801_; 
lean_del_object(v___x_3790_);
v_a_3796_ = lean_ctor_get(v_a_3788_, 0);
lean_inc(v_a_3796_);
lean_dec_ref_known(v_a_3788_, 1);
v___x_3797_ = lean_box(0);
v___x_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
lean_ctor_set(v___x_3798_, 1, v_a_3796_);
v_sz_3799_ = lean_array_size(v_tail_3786_);
v___x_3800_ = ((size_t)0ULL);
v___x_3801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_3777_, v_tail_3786_, v_sz_3799_, v___x_3800_, v___x_3798_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3815_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3804_ = v___x_3801_;
v_isShared_3805_ = v_isSharedCheck_3815_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3801_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3815_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v_fst_3806_; 
v_fst_3806_ = lean_ctor_get(v_a_3802_, 0);
if (lean_obj_tag(v_fst_3806_) == 0)
{
lean_object* v_snd_3807_; lean_object* v___x_3809_; 
v_snd_3807_ = lean_ctor_get(v_a_3802_, 1);
lean_inc(v_snd_3807_);
lean_dec(v_a_3802_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v_snd_3807_);
v___x_3809_ = v___x_3804_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_snd_3807_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
else
{
lean_object* v_val_3811_; lean_object* v___x_3813_; 
lean_inc_ref(v_fst_3806_);
lean_dec(v_a_3802_);
v_val_3811_ = lean_ctor_get(v_fst_3806_, 0);
lean_inc(v_val_3811_);
lean_dec_ref_known(v_fst_3806_, 1);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v_val_3811_);
v___x_3813_ = v___x_3804_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_val_3811_);
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
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
v_a_3816_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3801_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3801_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
v_a_3825_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3787_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3787_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(lean_object* v_elimTrivial_3833_, lean_object* v_t_3834_, lean_object* v_init_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
uint8_t v_elimTrivial_boxed_3841_; lean_object* v_res_3842_; 
v_elimTrivial_boxed_3841_ = lean_unbox(v_elimTrivial_3833_);
v_res_3842_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_boxed_3841_, v_t_3834_, v_init_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec_ref(v_t_3834_);
return v_res_3842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(lean_object* v_as_3843_, size_t v_sz_3844_, size_t v_i_3845_, lean_object* v_b_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
uint8_t v___x_3852_; 
v___x_3852_ = lean_usize_dec_lt(v_i_3845_, v_sz_3844_);
if (v___x_3852_ == 0)
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3853_, 0, v_b_3846_);
return v___x_3853_;
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v_a_3854_ = lean_array_uget_borrowed(v_as_3843_, v_i_3845_);
v___x_3855_ = l_Lean_Expr_fvarId_x21(v_a_3854_);
v___x_3856_ = l_Lean_MVarId_tryClear(v_b_3846_, v___x_3855_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; size_t v___x_3858_; size_t v___x_3859_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref_known(v___x_3856_, 1);
v___x_3858_ = ((size_t)1ULL);
v___x_3859_ = lean_usize_add(v_i_3845_, v___x_3858_);
v_i_3845_ = v___x_3859_;
v_b_3846_ = v_a_3857_;
goto _start;
}
else
{
return v___x_3856_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(lean_object* v_as_3861_, lean_object* v_sz_3862_, lean_object* v_i_3863_, lean_object* v_b_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
size_t v_sz_boxed_3870_; size_t v_i_boxed_3871_; lean_object* v_res_3872_; 
v_sz_boxed_3870_ = lean_unbox_usize(v_sz_3862_);
lean_dec(v_sz_3862_);
v_i_boxed_3871_ = lean_unbox_usize(v_i_3863_);
lean_dec(v_i_3863_);
v_res_3872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_as_3861_, v_sz_boxed_3870_, v_i_boxed_3871_, v_b_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec_ref(v_as_3861_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(lean_object* v_x_3873_, lean_object* v_x_3874_, lean_object* v_x_3875_, lean_object* v_x_3876_){
_start:
{
lean_object* v_ks_3877_; lean_object* v_vs_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3902_; 
v_ks_3877_ = lean_ctor_get(v_x_3873_, 0);
v_vs_3878_ = lean_ctor_get(v_x_3873_, 1);
v_isSharedCheck_3902_ = !lean_is_exclusive(v_x_3873_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3880_ = v_x_3873_;
v_isShared_3881_ = v_isSharedCheck_3902_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_vs_3878_);
lean_inc(v_ks_3877_);
lean_dec(v_x_3873_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3902_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3882_; uint8_t v___x_3883_; 
v___x_3882_ = lean_array_get_size(v_ks_3877_);
v___x_3883_ = lean_nat_dec_lt(v_x_3874_, v___x_3882_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3887_; 
lean_dec(v_x_3874_);
v___x_3884_ = lean_array_push(v_ks_3877_, v_x_3875_);
v___x_3885_ = lean_array_push(v_vs_3878_, v_x_3876_);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 1, v___x_3885_);
lean_ctor_set(v___x_3880_, 0, v___x_3884_);
v___x_3887_ = v___x_3880_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3888_, 1, v___x_3885_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
else
{
lean_object* v_k_x27_3889_; uint8_t v___x_3890_; 
v_k_x27_3889_ = lean_array_fget_borrowed(v_ks_3877_, v_x_3874_);
v___x_3890_ = l_Lean_instBEqMVarId_beq(v_x_3875_, v_k_x27_3889_);
if (v___x_3890_ == 0)
{
lean_object* v___x_3892_; 
if (v_isShared_3881_ == 0)
{
v___x_3892_ = v___x_3880_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_ks_3877_);
lean_ctor_set(v_reuseFailAlloc_3896_, 1, v_vs_3878_);
v___x_3892_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3893_ = lean_unsigned_to_nat(1u);
v___x_3894_ = lean_nat_add(v_x_3874_, v___x_3893_);
lean_dec(v_x_3874_);
v_x_3873_ = v___x_3892_;
v_x_3874_ = v___x_3894_;
goto _start;
}
}
else
{
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3900_; 
v___x_3897_ = lean_array_fset(v_ks_3877_, v_x_3874_, v_x_3875_);
v___x_3898_ = lean_array_fset(v_vs_3878_, v_x_3874_, v_x_3876_);
lean_dec(v_x_3874_);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 1, v___x_3898_);
lean_ctor_set(v___x_3880_, 0, v___x_3897_);
v___x_3900_ = v___x_3880_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3897_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v___x_3898_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(lean_object* v_n_3903_, lean_object* v_k_3904_, lean_object* v_v_3905_){
_start:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = lean_unsigned_to_nat(0u);
v___x_3907_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_n_3903_, v___x_3906_, v_k_3904_, v_v_3905_);
return v___x_3907_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_3908_; 
v___x_3908_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(lean_object* v_x_3909_, size_t v_x_3910_, size_t v_x_3911_, lean_object* v_x_3912_, lean_object* v_x_3913_){
_start:
{
if (lean_obj_tag(v_x_3909_) == 0)
{
lean_object* v_es_3914_; size_t v___x_3915_; size_t v___x_3916_; lean_object* v_j_3917_; lean_object* v___x_3918_; uint8_t v___x_3919_; 
v_es_3914_ = lean_ctor_get(v_x_3909_, 0);
v___x_3915_ = ((size_t)31ULL);
v___x_3916_ = lean_usize_land(v_x_3910_, v___x_3915_);
v_j_3917_ = lean_usize_to_nat(v___x_3916_);
v___x_3918_ = lean_array_get_size(v_es_3914_);
v___x_3919_ = lean_nat_dec_lt(v_j_3917_, v___x_3918_);
if (v___x_3919_ == 0)
{
lean_dec(v_j_3917_);
lean_dec(v_x_3913_);
lean_dec(v_x_3912_);
return v_x_3909_;
}
else
{
lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3958_; 
lean_inc_ref(v_es_3914_);
v_isSharedCheck_3958_ = !lean_is_exclusive(v_x_3909_);
if (v_isSharedCheck_3958_ == 0)
{
lean_object* v_unused_3959_; 
v_unused_3959_ = lean_ctor_get(v_x_3909_, 0);
lean_dec(v_unused_3959_);
v___x_3921_ = v_x_3909_;
v_isShared_3922_ = v_isSharedCheck_3958_;
goto v_resetjp_3920_;
}
else
{
lean_dec(v_x_3909_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3958_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v_v_3923_; lean_object* v___x_3924_; lean_object* v_xs_x27_3925_; lean_object* v___y_3927_; 
v_v_3923_ = lean_array_fget(v_es_3914_, v_j_3917_);
v___x_3924_ = lean_box(0);
v_xs_x27_3925_ = lean_array_fset(v_es_3914_, v_j_3917_, v___x_3924_);
switch(lean_obj_tag(v_v_3923_))
{
case 0:
{
lean_object* v_key_3932_; lean_object* v_val_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3943_; 
v_key_3932_ = lean_ctor_get(v_v_3923_, 0);
v_val_3933_ = lean_ctor_get(v_v_3923_, 1);
v_isSharedCheck_3943_ = !lean_is_exclusive(v_v_3923_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3935_ = v_v_3923_;
v_isShared_3936_ = v_isSharedCheck_3943_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_val_3933_);
lean_inc(v_key_3932_);
lean_dec(v_v_3923_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3943_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
uint8_t v___x_3937_; 
v___x_3937_ = l_Lean_instBEqMVarId_beq(v_x_3912_, v_key_3932_);
if (v___x_3937_ == 0)
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
lean_del_object(v___x_3935_);
v___x_3938_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3932_, v_val_3933_, v_x_3912_, v_x_3913_);
v___x_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3938_);
v___y_3927_ = v___x_3939_;
goto v___jp_3926_;
}
else
{
lean_object* v___x_3941_; 
lean_dec(v_val_3933_);
lean_dec(v_key_3932_);
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 1, v_x_3913_);
lean_ctor_set(v___x_3935_, 0, v_x_3912_);
v___x_3941_ = v___x_3935_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_x_3912_);
lean_ctor_set(v_reuseFailAlloc_3942_, 1, v_x_3913_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
v___y_3927_ = v___x_3941_;
goto v___jp_3926_;
}
}
}
}
case 1:
{
lean_object* v_node_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3956_; 
v_node_3944_ = lean_ctor_get(v_v_3923_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v_v_3923_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3946_ = v_v_3923_;
v_isShared_3947_ = v_isSharedCheck_3956_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_node_3944_);
lean_dec(v_v_3923_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3956_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
size_t v___x_3948_; size_t v___x_3949_; size_t v___x_3950_; size_t v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3954_; 
v___x_3948_ = ((size_t)5ULL);
v___x_3949_ = lean_usize_shift_right(v_x_3910_, v___x_3948_);
v___x_3950_ = ((size_t)1ULL);
v___x_3951_ = lean_usize_add(v_x_3911_, v___x_3950_);
v___x_3952_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_node_3944_, v___x_3949_, v___x_3951_, v_x_3912_, v_x_3913_);
if (v_isShared_3947_ == 0)
{
lean_ctor_set(v___x_3946_, 0, v___x_3952_);
v___x_3954_ = v___x_3946_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v___x_3952_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
v___y_3927_ = v___x_3954_;
goto v___jp_3926_;
}
}
}
default: 
{
lean_object* v___x_3957_; 
v___x_3957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3957_, 0, v_x_3912_);
lean_ctor_set(v___x_3957_, 1, v_x_3913_);
v___y_3927_ = v___x_3957_;
goto v___jp_3926_;
}
}
v___jp_3926_:
{
lean_object* v___x_3928_; lean_object* v___x_3930_; 
v___x_3928_ = lean_array_fset(v_xs_x27_3925_, v_j_3917_, v___y_3927_);
lean_dec(v_j_3917_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 0, v___x_3928_);
v___x_3930_ = v___x_3921_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3928_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
}
else
{
lean_object* v_ks_3960_; lean_object* v_vs_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3981_; 
v_ks_3960_ = lean_ctor_get(v_x_3909_, 0);
v_vs_3961_ = lean_ctor_get(v_x_3909_, 1);
v_isSharedCheck_3981_ = !lean_is_exclusive(v_x_3909_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3963_ = v_x_3909_;
v_isShared_3964_ = v_isSharedCheck_3981_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_vs_3961_);
lean_inc(v_ks_3960_);
lean_dec(v_x_3909_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3981_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3966_; 
if (v_isShared_3964_ == 0)
{
v___x_3966_ = v___x_3963_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_ks_3960_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v_vs_3961_);
v___x_3966_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
lean_object* v_newNode_3967_; uint8_t v___y_3969_; size_t v___x_3975_; uint8_t v___x_3976_; 
v_newNode_3967_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v___x_3966_, v_x_3912_, v_x_3913_);
v___x_3975_ = ((size_t)7ULL);
v___x_3976_ = lean_usize_dec_le(v___x_3975_, v_x_3911_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; lean_object* v___x_3978_; uint8_t v___x_3979_; 
v___x_3977_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3967_);
v___x_3978_ = lean_unsigned_to_nat(4u);
v___x_3979_ = lean_nat_dec_lt(v___x_3977_, v___x_3978_);
lean_dec(v___x_3977_);
v___y_3969_ = v___x_3979_;
goto v___jp_3968_;
}
else
{
v___y_3969_ = v___x_3976_;
goto v___jp_3968_;
}
v___jp_3968_:
{
if (v___y_3969_ == 0)
{
lean_object* v_ks_3970_; lean_object* v_vs_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v_ks_3970_ = lean_ctor_get(v_newNode_3967_, 0);
lean_inc_ref(v_ks_3970_);
v_vs_3971_ = lean_ctor_get(v_newNode_3967_, 1);
lean_inc_ref(v_vs_3971_);
lean_dec_ref(v_newNode_3967_);
v___x_3972_ = lean_unsigned_to_nat(0u);
v___x_3973_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0);
v___x_3974_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_x_3911_, v_ks_3970_, v_vs_3971_, v___x_3972_, v___x_3973_);
lean_dec_ref(v_vs_3971_);
lean_dec_ref(v_ks_3970_);
return v___x_3974_;
}
else
{
return v_newNode_3967_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(size_t v_depth_3982_, lean_object* v_keys_3983_, lean_object* v_vals_3984_, lean_object* v_i_3985_, lean_object* v_entries_3986_){
_start:
{
lean_object* v___x_3987_; uint8_t v___x_3988_; 
v___x_3987_ = lean_array_get_size(v_keys_3983_);
v___x_3988_ = lean_nat_dec_lt(v_i_3985_, v___x_3987_);
if (v___x_3988_ == 0)
{
lean_dec(v_i_3985_);
return v_entries_3986_;
}
else
{
lean_object* v_k_3989_; lean_object* v_v_3990_; uint64_t v___x_3991_; size_t v_h_3992_; size_t v___x_3993_; lean_object* v___x_3994_; size_t v___x_3995_; size_t v___x_3996_; size_t v___x_3997_; size_t v_h_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v_k_3989_ = lean_array_fget_borrowed(v_keys_3983_, v_i_3985_);
v_v_3990_ = lean_array_fget_borrowed(v_vals_3984_, v_i_3985_);
v___x_3991_ = l_Lean_instHashableMVarId_hash(v_k_3989_);
v_h_3992_ = lean_uint64_to_usize(v___x_3991_);
v___x_3993_ = ((size_t)5ULL);
v___x_3994_ = lean_unsigned_to_nat(1u);
v___x_3995_ = ((size_t)1ULL);
v___x_3996_ = lean_usize_sub(v_depth_3982_, v___x_3995_);
v___x_3997_ = lean_usize_mul(v___x_3993_, v___x_3996_);
v_h_3998_ = lean_usize_shift_right(v_h_3992_, v___x_3997_);
v___x_3999_ = lean_nat_add(v_i_3985_, v___x_3994_);
lean_dec(v_i_3985_);
lean_inc(v_v_3990_);
lean_inc(v_k_3989_);
v___x_4000_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_entries_3986_, v_h_3998_, v_depth_3982_, v_k_3989_, v_v_3990_);
v_i_3985_ = v___x_3999_;
v_entries_3986_ = v___x_4000_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_depth_4002_, lean_object* v_keys_4003_, lean_object* v_vals_4004_, lean_object* v_i_4005_, lean_object* v_entries_4006_){
_start:
{
size_t v_depth_boxed_4007_; lean_object* v_res_4008_; 
v_depth_boxed_4007_ = lean_unbox_usize(v_depth_4002_);
lean_dec(v_depth_4002_);
v_res_4008_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_boxed_4007_, v_keys_4003_, v_vals_4004_, v_i_4005_, v_entries_4006_);
lean_dec_ref(v_vals_4004_);
lean_dec_ref(v_keys_4003_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_x_4009_, lean_object* v_x_4010_, lean_object* v_x_4011_, lean_object* v_x_4012_, lean_object* v_x_4013_){
_start:
{
size_t v_x_7958__boxed_4014_; size_t v_x_7959__boxed_4015_; lean_object* v_res_4016_; 
v_x_7958__boxed_4014_ = lean_unbox_usize(v_x_4010_);
lean_dec(v_x_4010_);
v_x_7959__boxed_4015_ = lean_unbox_usize(v_x_4011_);
lean_dec(v_x_4011_);
v_res_4016_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4009_, v_x_7958__boxed_4014_, v_x_7959__boxed_4015_, v_x_4012_, v_x_4013_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(lean_object* v_x_4017_, lean_object* v_x_4018_, lean_object* v_x_4019_){
_start:
{
uint64_t v___x_4020_; size_t v___x_4021_; size_t v___x_4022_; lean_object* v___x_4023_; 
v___x_4020_ = l_Lean_instHashableMVarId_hash(v_x_4018_);
v___x_4021_ = lean_uint64_to_usize(v___x_4020_);
v___x_4022_ = ((size_t)1ULL);
v___x_4023_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4017_, v___x_4021_, v___x_4022_, v_x_4018_, v_x_4019_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(lean_object* v_mvarId_4024_, lean_object* v_val_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v___x_4028_; lean_object* v_mctx_4029_; lean_object* v_cache_4030_; lean_object* v_zetaDeltaFVarIds_4031_; lean_object* v_postponed_4032_; lean_object* v_diag_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4061_; 
v___x_4028_ = lean_st_ref_take(v___y_4026_);
v_mctx_4029_ = lean_ctor_get(v___x_4028_, 0);
v_cache_4030_ = lean_ctor_get(v___x_4028_, 1);
v_zetaDeltaFVarIds_4031_ = lean_ctor_get(v___x_4028_, 2);
v_postponed_4032_ = lean_ctor_get(v___x_4028_, 3);
v_diag_4033_ = lean_ctor_get(v___x_4028_, 4);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4035_ = v___x_4028_;
v_isShared_4036_ = v_isSharedCheck_4061_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_diag_4033_);
lean_inc(v_postponed_4032_);
lean_inc(v_zetaDeltaFVarIds_4031_);
lean_inc(v_cache_4030_);
lean_inc(v_mctx_4029_);
lean_dec(v___x_4028_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4061_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v_depth_4037_; lean_object* v_levelAssignDepth_4038_; lean_object* v_lmvarCounter_4039_; lean_object* v_mvarCounter_4040_; lean_object* v_lDecls_4041_; lean_object* v_decls_4042_; lean_object* v_userNames_4043_; lean_object* v_lAssignment_4044_; lean_object* v_eAssignment_4045_; lean_object* v_dAssignment_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4060_; 
v_depth_4037_ = lean_ctor_get(v_mctx_4029_, 0);
v_levelAssignDepth_4038_ = lean_ctor_get(v_mctx_4029_, 1);
v_lmvarCounter_4039_ = lean_ctor_get(v_mctx_4029_, 2);
v_mvarCounter_4040_ = lean_ctor_get(v_mctx_4029_, 3);
v_lDecls_4041_ = lean_ctor_get(v_mctx_4029_, 4);
v_decls_4042_ = lean_ctor_get(v_mctx_4029_, 5);
v_userNames_4043_ = lean_ctor_get(v_mctx_4029_, 6);
v_lAssignment_4044_ = lean_ctor_get(v_mctx_4029_, 7);
v_eAssignment_4045_ = lean_ctor_get(v_mctx_4029_, 8);
v_dAssignment_4046_ = lean_ctor_get(v_mctx_4029_, 9);
v_isSharedCheck_4060_ = !lean_is_exclusive(v_mctx_4029_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4048_ = v_mctx_4029_;
v_isShared_4049_ = v_isSharedCheck_4060_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_dAssignment_4046_);
lean_inc(v_eAssignment_4045_);
lean_inc(v_lAssignment_4044_);
lean_inc(v_userNames_4043_);
lean_inc(v_decls_4042_);
lean_inc(v_lDecls_4041_);
lean_inc(v_mvarCounter_4040_);
lean_inc(v_lmvarCounter_4039_);
lean_inc(v_levelAssignDepth_4038_);
lean_inc(v_depth_4037_);
lean_dec(v_mctx_4029_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4060_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4050_; lean_object* v___x_4052_; 
v___x_4050_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_eAssignment_4045_, v_mvarId_4024_, v_val_4025_);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 8, v___x_4050_);
v___x_4052_ = v___x_4048_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_depth_4037_);
lean_ctor_set(v_reuseFailAlloc_4059_, 1, v_levelAssignDepth_4038_);
lean_ctor_set(v_reuseFailAlloc_4059_, 2, v_lmvarCounter_4039_);
lean_ctor_set(v_reuseFailAlloc_4059_, 3, v_mvarCounter_4040_);
lean_ctor_set(v_reuseFailAlloc_4059_, 4, v_lDecls_4041_);
lean_ctor_set(v_reuseFailAlloc_4059_, 5, v_decls_4042_);
lean_ctor_set(v_reuseFailAlloc_4059_, 6, v_userNames_4043_);
lean_ctor_set(v_reuseFailAlloc_4059_, 7, v_lAssignment_4044_);
lean_ctor_set(v_reuseFailAlloc_4059_, 8, v___x_4050_);
lean_ctor_set(v_reuseFailAlloc_4059_, 9, v_dAssignment_4046_);
v___x_4052_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_object* v___x_4054_; 
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v___x_4052_);
v___x_4054_ = v___x_4035_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v___x_4052_);
lean_ctor_set(v_reuseFailAlloc_4058_, 1, v_cache_4030_);
lean_ctor_set(v_reuseFailAlloc_4058_, 2, v_zetaDeltaFVarIds_4031_);
lean_ctor_set(v_reuseFailAlloc_4058_, 3, v_postponed_4032_);
lean_ctor_set(v_reuseFailAlloc_4058_, 4, v_diag_4033_);
v___x_4054_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; 
v___x_4055_ = lean_st_ref_set(v___y_4026_, v___x_4054_);
v___x_4056_ = lean_box(0);
v___x_4057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4056_);
return v___x_4057_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(lean_object* v_mvarId_4062_, lean_object* v_val_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4062_, v_val_4063_, v___y_4064_);
lean_dec(v___y_4064_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0(lean_object* v_mvar_4069_, uint8_t v_elimTrivial_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v___x_4076_; 
lean_inc(v_mvar_4069_);
v___x_4076_ = l_Lean_MVarId_getType(v_mvar_4069_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4077_);
lean_dec_ref_known(v___x_4076_, 1);
v___x_4078_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_4079_ = l_Lean_Elab_Tactic_Do_countUses(v_a_4077_, v___x_4078_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v_fst_4081_; lean_object* v_snd_4082_; lean_object* v_lctx_4083_; lean_object* v___x_4084_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___x_4079_, 1);
v_fst_4081_ = lean_ctor_get(v_a_4080_, 0);
lean_inc(v_fst_4081_);
v_snd_4082_ = lean_ctor_get(v_a_4080_, 1);
lean_inc(v_snd_4082_);
lean_dec(v_a_4080_);
v_lctx_4083_ = lean_ctor_get(v___y_4071_, 2);
lean_inc_ref(v_lctx_4083_);
v___x_4084_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_lctx_4083_, v_snd_4082_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v_a_4085_; lean_object* v___x_4086_; lean_object* v_decls_4087_; lean_object* v___x_4088_; 
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
lean_inc(v_a_4085_);
lean_dec_ref_known(v___x_4084_, 1);
v___x_4086_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0));
v_decls_4087_ = lean_ctor_get(v_a_4085_, 1);
lean_inc_ref(v_decls_4087_);
lean_dec(v_a_4085_);
v___x_4088_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_4070_, v_decls_4087_, v___x_4086_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
lean_dec_ref(v_decls_4087_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v_a_4089_; lean_object* v_fst_4090_; lean_object* v_snd_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v_a_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref_known(v___x_4088_, 1);
v_fst_4090_ = lean_ctor_get(v_a_4089_, 0);
lean_inc(v_fst_4090_);
v_snd_4091_ = lean_ctor_get(v_a_4089_, 1);
lean_inc(v_snd_4091_);
lean_dec(v_a_4089_);
v___x_4092_ = l_Lean_Expr_replaceFVars(v_fst_4081_, v_fst_4090_, v_snd_4091_);
lean_dec(v_snd_4091_);
lean_dec(v_fst_4081_);
v___x_4093_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v___x_4092_, v_elimTrivial_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v_a_4094_; lean_object* v___x_4095_; 
v_a_4094_ = lean_ctor_get(v___x_4093_, 0);
lean_inc(v_a_4094_);
lean_dec_ref_known(v___x_4093_, 1);
lean_inc(v_mvar_4069_);
v___x_4095_ = l_Lean_MVarId_getTag(v_mvar_4069_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v_a_4096_; lean_object* v___x_4097_; 
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
lean_inc(v_a_4096_);
lean_dec_ref_known(v___x_4095_, 1);
v___x_4097_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4094_, v_a_4096_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_a_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; size_t v_sz_4101_; size_t v___x_4102_; lean_object* v___x_4103_; 
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
lean_inc_n(v_a_4098_, 2);
lean_dec_ref_known(v___x_4097_, 1);
v___x_4099_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvar_4069_, v_a_4098_, v___y_4072_);
lean_dec_ref(v___x_4099_);
v___x_4100_ = l_Lean_Expr_mvarId_x21(v_a_4098_);
lean_dec(v_a_4098_);
v_sz_4101_ = lean_array_size(v_fst_4090_);
v___x_4102_ = ((size_t)0ULL);
v___x_4103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_fst_4090_, v_sz_4101_, v___x_4102_, v___x_4100_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
lean_dec_ref(v___y_4071_);
lean_dec(v_fst_4090_);
return v___x_4103_;
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_dec(v_fst_4090_);
lean_dec_ref(v___y_4071_);
lean_dec(v_mvar_4069_);
v_a_4104_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4097_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4097_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
else
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4119_; 
lean_dec(v_a_4094_);
lean_dec(v_fst_4090_);
lean_dec_ref(v___y_4071_);
lean_dec(v_mvar_4069_);
v_a_4112_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4114_ = v___x_4095_;
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_4095_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4117_; 
if (v_isShared_4115_ == 0)
{
v___x_4117_ = v___x_4114_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_a_4112_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
else
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
lean_dec(v_fst_4090_);
lean_dec_ref(v___y_4071_);
lean_dec(v_mvar_4069_);
v_a_4120_ = lean_ctor_get(v___x_4093_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4122_ = v___x_4093_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4093_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
else
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4135_; 
lean_dec(v_fst_4081_);
lean_dec_ref(v___y_4071_);
lean_dec(v_mvar_4069_);
v_a_4128_ = lean_ctor_get(v___x_4088_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4088_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4130_ = v___x_4088_;
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4088_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4133_; 
if (v_isShared_4131_ == 0)
{
v___x_4133_ = v___x_4130_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_a_4128_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_dec(v_fst_4081_);
lean_dec_ref(v___y_4071_);
lean_dec(v_mvar_4069_);
v_a_4136_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4084_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4084_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
lean_dec_ref(v___y_4071_);
lean_dec(v_mvar_4069_);
v_a_4144_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_4079_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4079_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
else
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
lean_dec_ref(v___y_4071_);
lean_dec(v_mvar_4069_);
v_a_4152_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4154_ = v___x_4076_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4076_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4152_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(lean_object* v_mvar_4160_, lean_object* v_elimTrivial_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
uint8_t v_elimTrivial_boxed_4167_; lean_object* v_res_4168_; 
v_elimTrivial_boxed_4167_ = lean_unbox(v_elimTrivial_4161_);
v_res_4168_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0(v_mvar_4160_, v_elimTrivial_boxed_4167_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
lean_dec(v___y_4163_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets(lean_object* v_mvar_4169_, uint8_t v_elimTrivial_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_){
_start:
{
lean_object* v___x_4176_; lean_object* v___f_4177_; lean_object* v___x_4178_; 
v___x_4176_ = lean_box(v_elimTrivial_4170_);
lean_inc(v_mvar_4169_);
v___f_4177_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4177_, 0, v_mvar_4169_);
lean_closure_set(v___f_4177_, 1, v___x_4176_);
v___x_4178_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvar_4169_, v___f_4177_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_);
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___boxed(lean_object* v_mvar_4179_, lean_object* v_elimTrivial_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
uint8_t v_elimTrivial_boxed_4186_; lean_object* v_res_4187_; 
v_elimTrivial_boxed_4186_ = lean_unbox(v_elimTrivial_4180_);
v_res_4187_ = l_Lean_Elab_Tactic_Do_elimLets(v_mvar_4179_, v_elimTrivial_boxed_4186_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_);
lean_dec(v_a_4184_);
lean_dec_ref(v_a_4183_);
lean_dec(v_a_4182_);
lean_dec_ref(v_a_4181_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(lean_object* v_mvarId_4188_, lean_object* v_val_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v___x_4195_; 
v___x_4195_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4188_, v_val_4189_, v___y_4191_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(lean_object* v_mvarId_4196_, lean_object* v_val_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(v_mvarId_4196_, v_val_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(lean_object* v_00_u03b2_4204_, lean_object* v_x_4205_, lean_object* v_x_4206_, lean_object* v_x_4207_){
_start:
{
lean_object* v___x_4208_; 
v___x_4208_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_x_4205_, v_x_4206_, v_x_4207_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(uint8_t v_elimTrivial_4209_, lean_object* v_as_4210_, size_t v_sz_4211_, size_t v_i_4212_, lean_object* v_b_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v___x_4219_; 
v___x_4219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_4209_, v_as_4210_, v_sz_4211_, v_i_4212_, v_b_4213_);
return v___x_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(lean_object* v_elimTrivial_4220_, lean_object* v_as_4221_, lean_object* v_sz_4222_, lean_object* v_i_4223_, lean_object* v_b_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
uint8_t v_elimTrivial_boxed_4230_; size_t v_sz_boxed_4231_; size_t v_i_boxed_4232_; lean_object* v_res_4233_; 
v_elimTrivial_boxed_4230_ = lean_unbox(v_elimTrivial_4220_);
v_sz_boxed_4231_ = lean_unbox_usize(v_sz_4222_);
lean_dec(v_sz_4222_);
v_i_boxed_4232_ = lean_unbox_usize(v_i_4223_);
lean_dec(v_i_4223_);
v_res_4233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(v_elimTrivial_boxed_4230_, v_as_4221_, v_sz_boxed_4231_, v_i_boxed_4232_, v_b_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_);
lean_dec(v___y_4228_);
lean_dec_ref(v___y_4227_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
lean_dec_ref(v_as_4221_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_4234_, lean_object* v_x_4235_, size_t v_x_4236_, size_t v_x_4237_, lean_object* v_x_4238_, lean_object* v_x_4239_){
_start:
{
lean_object* v___x_4240_; 
v___x_4240_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4235_, v_x_4236_, v_x_4237_, v_x_4238_, v_x_4239_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_4241_, lean_object* v_x_4242_, lean_object* v_x_4243_, lean_object* v_x_4244_, lean_object* v_x_4245_, lean_object* v_x_4246_){
_start:
{
size_t v_x_8408__boxed_4247_; size_t v_x_8409__boxed_4248_; lean_object* v_res_4249_; 
v_x_8408__boxed_4247_ = lean_unbox_usize(v_x_4243_);
lean_dec(v_x_4243_);
v_x_8409__boxed_4248_ = lean_unbox_usize(v_x_4244_);
lean_dec(v_x_4244_);
v_res_4249_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(v_00_u03b2_4241_, v_x_4242_, v_x_8408__boxed_4247_, v_x_8409__boxed_4248_, v_x_4245_, v_x_4246_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(uint8_t v_elimTrivial_4250_, lean_object* v_as_4251_, size_t v_sz_4252_, size_t v_i_4253_, lean_object* v_b_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_4250_, v_as_4251_, v_sz_4252_, v_i_4253_, v_b_4254_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(lean_object* v_elimTrivial_4261_, lean_object* v_as_4262_, lean_object* v_sz_4263_, lean_object* v_i_4264_, lean_object* v_b_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
uint8_t v_elimTrivial_boxed_4271_; size_t v_sz_boxed_4272_; size_t v_i_boxed_4273_; lean_object* v_res_4274_; 
v_elimTrivial_boxed_4271_ = lean_unbox(v_elimTrivial_4261_);
v_sz_boxed_4272_ = lean_unbox_usize(v_sz_4263_);
lean_dec(v_sz_4263_);
v_i_boxed_4273_ = lean_unbox_usize(v_i_4264_);
lean_dec(v_i_4264_);
v_res_4274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(v_elimTrivial_boxed_4271_, v_as_4262_, v_sz_boxed_4272_, v_i_boxed_4273_, v_b_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec_ref(v_as_4262_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(lean_object* v_00_u03b2_4275_, lean_object* v_n_4276_, lean_object* v_k_4277_, lean_object* v_v_4278_){
_start:
{
lean_object* v___x_4279_; 
v___x_4279_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v_n_4276_, v_k_4277_, v_v_4278_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_4280_, size_t v_depth_4281_, lean_object* v_keys_4282_, lean_object* v_vals_4283_, lean_object* v_heq_4284_, lean_object* v_i_4285_, lean_object* v_entries_4286_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_4281_, v_keys_4282_, v_vals_4283_, v_i_4285_, v_entries_4286_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_4288_, lean_object* v_depth_4289_, lean_object* v_keys_4290_, lean_object* v_vals_4291_, lean_object* v_heq_4292_, lean_object* v_i_4293_, lean_object* v_entries_4294_){
_start:
{
size_t v_depth_boxed_4295_; lean_object* v_res_4296_; 
v_depth_boxed_4295_ = lean_unbox_usize(v_depth_4289_);
lean_dec(v_depth_4289_);
v_res_4296_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_4288_, v_depth_boxed_4295_, v_keys_4290_, v_vals_4291_, v_heq_4292_, v_i_4293_, v_entries_4294_);
lean_dec_ref(v_vals_4291_);
lean_dec_ref(v_keys_4290_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_4297_, lean_object* v_x_4298_, lean_object* v_x_4299_, lean_object* v_x_4300_, lean_object* v_x_4301_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_x_4298_, v_x_4299_, v_x_4300_, v_x_4301_);
return v___x_4302_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_LetElim(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
